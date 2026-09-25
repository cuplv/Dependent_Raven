// Trial file: the CSCI 3155 Project 1 stack-machine compiler
// Copy into tests/ to work on it; this file itself is never edited during a trial.
#[ravencheck::module]
mod compiler_spec {

    // ---- 1. Peano naturals (instruction counts and list lengths) ----
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    // ---- 2. Numbers: Peano naturals with the operations defined inductively ----
    // The notebook's values are Scala Doubles and the instructions call the
    // primitive `+ - * / >= >`; here `Num` is `Nat` and every operation is a
    // recursive definition, as in the F* and Lean transcriptions. `sub` is
    // truncated subtraction, `div` is floor division by repeated subtraction
    // (a division by zero is caught before it, so `div_pos` is only called
    // with a non-zero divisor).
    #[val]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x1) => Nat::S(Box::new(add(*x1, y))),
        }
    }

    #[val]
    #[recursive]
    fn mul(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => Nat::Z,
            Nat::S(x1) => add(y.clone(), mul(*x1, y)),
        }
    }

    // truncated: sub(x, y) = 0 when y >= x
    #[val]
    #[recursive]
    fn sub(x: Nat, y: Nat) -> Nat {
        match y {
            Nat::Z => x,
            Nat::S(y1) => match x {
                Nat::Z => Nat::Z,
                Nat::S(x1) => sub(*x1, *y1),
            },
        }
    }

    #[val]
    #[recursive]
    fn leq(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x1) => match y {
                Nat::Z => false,
                Nat::S(y1) => leq(*x1, *y1),
            },
        }
    }

    #[val]
    #[recursive]
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y1) => match x {
                Nat::Z => true,
                Nat::S(x1) => lt(*x1, *y1),
            },
        }
    }

    #[val]
    fn geq(x: Nat, y: Nat) -> bool {
        leq(y, x)
    }

    #[val]
    fn gt(x: Nat, y: Nat) -> bool {
        lt(y, x)
    }

    #[val]
    fn is_zero(x: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(_) => false,
        }
    }

    // floor division for a non-zero divisor: count how many times y fits
    #[val]
    #[recursive]
    fn div_pos(x: Nat, y: Nat) -> Nat {
        if lt(x.clone(), y.clone()) {
            Nat::Z
        } else {
            Nat::S(Box::new(div_pos(sub(x, y.clone()), y)))
        }
    }

    #[val]
    fn div(x: Nat, y: Nat) -> Nat {
        if is_zero(y.clone()) {
            Nat::Z
        } else {
            div_pos(x, y)
        }
    }

    // ---- 3. Identifiers ----
    #[declare]
    type Ident = String;

    // ---- 4. Values ----
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Value {
        Num(Nat),
        Bool(bool),
    }

    // ---- 5. The source language ----
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Expr {
        Const(Nat),
        Id(Ident),
        Add(Box<Expr>, Box<Expr>),
        Sub(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
        Div(Box<Expr>, Box<Expr>),
        Geq(Box<Expr>, Box<Expr>),
        Gt(Box<Expr>, Box<Expr>),
        Eq(Box<Expr>, Box<Expr>),
        And(Box<Expr>, Box<Expr>),
        Or(Box<Expr>, Box<Expr>),
        Not(Box<Expr>),
        IfThenElse(Box<Expr>, Box<Expr>, Box<Expr>),
        Let(Ident, Box<Expr>, Box<Expr>),
    }

    // ---- 6. The stack machine ----
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Instr {
        IPush(Nat),
        IPushBool(bool),
        IPlus,
        ISub,
        IMul,
        IDiv,
        IGeq,
        IGt,
        IEq,
        INot,
        IStore(Ident),
        ILoad(Ident),
        IPop,
        ICondSkip(Nat),
        ISkip(Nat),
    }
    // Instruction list
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum IList {
        INil,
        ICons(Instr, Box<IList>),
    }

    // Operand stack
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum VList {
        VNil,
        VCons(Value, Box<VList>),
    }

    // Environment stack: (identifier, value) pairs
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Env {
        ENil,
        ECons(Ident, Value, Box<Env>),
    }
    // Result for lookup function
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Look {
        Found(Value),
        Missing,
    }

    // Machine result: the two stacks, or an exception
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Res {
        Done(VList, Env),
        Fail,
    }

    // source result: a value, or an exception
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum EvRes {
        Ok(Value),
        Err,
    }

    // ---- 7. List helpers ----
    #[val]
    #[recursive]
    fn app(xs: IList, ys: IList) -> IList {
        match xs {
            IList::INil => ys,
            IList::ICons(i, t) => IList::ICons(i, Box::new(app(*t, ys))),
        }
    }

    #[val]
    #[recursive]
    fn length(xs: IList) -> Nat {
        match xs {
            IList::INil => Nat::Z,
            IList::ICons(_, t) => Nat::S(Box::new(length(*t))),
        }
    }

    // drop the first n instructions (all of them if fewer)
    #[val]
    #[recursive]
    fn drop(n: Nat, xs: IList) -> IList {
        match n {
            Nat::Z => xs,
            Nat::S(m) => match xs {
                IList::INil => IList::INil,
                IList::ICons(_, t) => drop(*m, *t),
            },
        }
    }

    // ILoad: scan the environment from the top for the first binding of x
    #[val]
    #[recursive]
    fn lookup(x: Ident, env: Env) -> Look {
        match env {
            Env::ENil => Look::Missing,
            Env::ECons(y, v, rest) => {
                if x == y {
                    Look::Found(v)
                } else {
                    lookup(x, *rest)
                }
            }
        }
    }

    // ---- 8. the emulator ----
    // exec(instructions, operand stack, environment stack). ISub/IDiv/IGeq/IGt
    // use the notebook's order: v1 is the top of the stack, v2 below it, and
    // the result is v2 op v1.
    #[val]
    #[recursive]
    fn exec(is: IList, ops: VList, env: Env) -> Res {
        match is {
            IList::INil => Res::Done(ops, env),
            IList::ICons(i, rest) => match i {
                Instr::IPush(d) => exec(*rest, VList::VCons(Value::Num(d), Box::new(ops)), env),
                Instr::IPushBool(b) => {
                    exec(*rest, VList::VCons(Value::Bool(b), Box::new(ops)), env)
                }
                Instr::IPlus => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                exec(*rest, VList::VCons(Value::Num(add(b, a)), t2), env)
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::ISub => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                exec(*rest, VList::VCons(Value::Num(sub(b, a)), t2), env)
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::IMul => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                exec(*rest, VList::VCons(Value::Num(mul(b, a)), t2), env)
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::IDiv => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                if is_zero(a.clone()) {
                                    Res::Fail
                                } else {
                                    exec(*rest, VList::VCons(Value::Num(div(b, a)), t2), env)
                                }
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::IGeq => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                exec(*rest, VList::VCons(Value::Bool(geq(b, a)), t2), env)
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::IGt => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => match (v1, v2) {
                            (Value::Num(a), Value::Num(b)) => {
                                exec(*rest, VList::VCons(Value::Bool(gt(b, a)), t2), env)
                            }
                            _ => Res::Fail,
                        },
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                // IEq compares any two values
                Instr::IEq => match ops {
                    VList::VCons(v1, t1) => match *t1 {
                        VList::VCons(v2, t2) => {
                            if v1 == v2 {
                                exec(*rest, VList::VCons(Value::Bool(true), t2), env)
                            } else {
                                exec(*rest, VList::VCons(Value::Bool(false), t2), env)
                            }
                        }
                        _ => Res::Fail,
                    },
                    _ => Res::Fail,
                },
                Instr::INot => match ops {
                    VList::VCons(Value::Bool(b), t) => {
                        exec(*rest, VList::VCons(Value::Bool(!b), t), env)
                    }
                    _ => Res::Fail,
                },
                Instr::IStore(x) => match ops {
                    VList::VCons(v, t) => exec(*rest, *t, Env::ECons(x, v, Box::new(env))),
                    _ => Res::Fail,
                },
                Instr::ILoad(x) => match lookup(x, env.clone()) {
                    Look::Found(v) => exec(*rest, VList::VCons(v, Box::new(ops)), env),
                    Look::Missing => Res::Fail,
                },
                Instr::IPop => match env {
                    Env::ECons(_, _, rest_env) => exec(*rest, ops, *rest_env),
                    _ => Res::Fail,
                },
                // pop a boolean; on false skip the next n instructions
                Instr::ICondSkip(n) => match ops {
                    VList::VCons(Value::Bool(true), t) => exec(*rest, *t, env),
                    VList::VCons(Value::Bool(false), t) => exec(drop(n, *rest), *t, env),
                    _ => Res::Fail,
                },
                Instr::ISkip(n) => exec(drop(n, *rest), ops, env),
            },
        }
    }

    // ---- 9. Source semantics ----
    #[val]
    #[recursive]
    fn eval(e: Expr, env: Env) -> EvRes {
        match e {
            Expr::Const(d) => EvRes::Ok(Value::Num(d)),
            Expr::Id(x) => match lookup(x, env) {
                Look::Found(v) => EvRes::Ok(v),
                Look::Missing => EvRes::Err,
            },
            Expr::Add(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    EvRes::Ok(Value::Num(add(a, b)))
                }
                _ => EvRes::Err,
            },
            Expr::Sub(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    EvRes::Ok(Value::Num(sub(a, b)))
                }
                _ => EvRes::Err,
            },
            Expr::Mul(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    EvRes::Ok(Value::Num(mul(a, b)))
                }
                _ => EvRes::Err,
            },
            Expr::Div(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    if is_zero(b.clone()) {
                        EvRes::Err
                    } else {
                        EvRes::Ok(Value::Num(div(a, b)))
                    }
                }
                _ => EvRes::Err,
            },
            Expr::Geq(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    EvRes::Ok(Value::Bool(geq(a, b)))
                }
                _ => EvRes::Err,
            },
            Expr::Gt(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(Value::Num(a)), EvRes::Ok(Value::Num(b))) => {
                    EvRes::Ok(Value::Bool(gt(a, b)))
                }
                _ => EvRes::Err,
            },
            Expr::Eq(e1, e2) => match (eval(*e1, env.clone()), eval(*e2, env)) {
                (EvRes::Ok(a), EvRes::Ok(b)) => {
                    if a == b {
                        EvRes::Ok(Value::Bool(true))
                    } else {
                        EvRes::Ok(Value::Bool(false))
                    }
                }
                _ => EvRes::Err,
            },
            // short circuit: `if e1 then e2 else false`
            Expr::And(e1, e2) => match eval(*e1, env.clone()) {
                EvRes::Ok(Value::Bool(true)) => eval(*e2, env),
                EvRes::Ok(Value::Bool(false)) => EvRes::Ok(Value::Bool(false)),
                _ => EvRes::Err,
            },
            // short circuit: `if e1 then true else e2`
            Expr::Or(e1, e2) => match eval(*e1, env.clone()) {
                EvRes::Ok(Value::Bool(true)) => EvRes::Ok(Value::Bool(true)),
                EvRes::Ok(Value::Bool(false)) => eval(*e2, env),
                _ => EvRes::Err,
            },
            Expr::Not(e1) => match eval(*e1, env) {
                EvRes::Ok(Value::Bool(b)) => EvRes::Ok(Value::Bool(!b)),
                _ => EvRes::Err,
            },
            Expr::IfThenElse(c, t, f) => match eval(*c, env.clone()) {
                EvRes::Ok(Value::Bool(true)) => eval(*t, env),
                EvRes::Ok(Value::Bool(false)) => eval(*f, env),
                _ => EvRes::Err,
            },
            Expr::Let(x, e1, e2) => match eval(*e1, env.clone()) {
                EvRes::Ok(v) => eval(*e2, Env::ECons(x, v, Box::new(env))),
                EvRes::Err => EvRes::Err,
            },
        }
    }

    // ---- 10. Compiler (based on notebook's rule) ----
    #[val]
    #[recursive]
    fn compile(e: Expr) -> IList {
        match e {
            Expr::Const(d) => IList::ICons(Instr::IPush(d), Box::new(IList::INil)),
            Expr::Id(x) => IList::ICons(Instr::ILoad(x), Box::new(IList::INil)),
            Expr::Add(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IPlus, Box::new(IList::INil)),
                ),
            ),
            Expr::Sub(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::ISub, Box::new(IList::INil)),
                ),
            ),
            Expr::Mul(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IMul, Box::new(IList::INil)),
                ),
            ),
            Expr::Div(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IDiv, Box::new(IList::INil)),
                ),
            ),
            Expr::Geq(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IGeq, Box::new(IList::INil)),
                ),
            ),
            Expr::Gt(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IGt, Box::new(IList::INil)),
                ),
            ),
            Expr::Eq(e1, e2) => app(
                compile(*e1),
                app(
                    compile(*e2),
                    IList::ICons(Instr::IEq, Box::new(IList::INil)),
                ),
            ),
            Expr::Not(e1) => app(
                compile(*e1),
                IList::ICons(Instr::INot, Box::new(IList::INil)),
            ),
            // L0 ; ICondSkip(len(L1)+1) ; L1 ; ISkip(len(L2)) ; L2
            Expr::IfThenElse(c, t, f) => {
                let l1 = compile(*t);
                let l2 = compile(*f);
                app(
                    compile(*c),
                    IList::ICons(
                        Instr::ICondSkip(Nat::S(Box::new(length(l1.clone())))),
                        Box::new(app(
                            l1,
                            IList::ICons(Instr::ISkip(length(l2.clone())), Box::new(l2)),
                        )),
                    ),
                )
            }
            // And(e1, e2) = IfThenElse(e1, e2, false):
            //   L1 ; ICondSkip(len(L2)+1) ; L2 ; ISkip(1) ; IPushBool(false)
            Expr::And(e1, e2) => {
                let l2 = compile(*e2);
                app(
                    compile(*e1),
                    IList::ICons(
                        Instr::ICondSkip(Nat::S(Box::new(length(l2.clone())))),
                        Box::new(app(
                            l2,
                            IList::ICons(
                                Instr::ISkip(Nat::S(Box::new(Nat::Z))),
                                Box::new(IList::ICons(
                                    Instr::IPushBool(false),
                                    Box::new(IList::INil),
                                )),
                            ),
                        )),
                    ),
                )
            }
            // Or(e1, e2) = IfThenElse(e1, true, e2):
            //   L1 ; ICondSkip(2) ; IPushBool(true) ; ISkip(len(L2)) ; L2
            Expr::Or(e1, e2) => {
                let l2 = compile(*e2);
                app(
                    compile(*e1),
                    IList::ICons(
                        Instr::ICondSkip(Nat::S(Box::new(Nat::S(Box::new(Nat::Z))))),
                        Box::new(IList::ICons(
                            Instr::IPushBool(true),
                            Box::new(IList::ICons(Instr::ISkip(length(l2.clone())), Box::new(l2))),
                        )),
                    ),
                )
            }
            // L1 ; IStore(x) ; L2 ; IPop
            Expr::Let(x, e1, e2) => app(
                compile(*e1),
                IList::ICons(
                    Instr::IStore(x),
                    Box::new(app(
                        compile(*e2),
                        IList::ICons(Instr::IPop, Box::new(IList::INil)),
                    )),
                ),
            ),
        }
    }

    // ---- 12. Goal theorem ----
    // If e evaluates to v in env, then running compile(e) followed by any
    // continuation `rest`, from any operand stack, is the same as running
    // `rest` with v pushed.
    //   eval(e, env) = Ok(v)
    //   ==> exec(compile(e) ++ rest, ops, env) = exec(rest, v :: ops, env)
    // Parameters:
    //  - `e`: The source expression to evaluate and compile.
    //  - `env`: The environment stack mapping identifiers to values.
    //  - `v`: The evaluated value of `e`.
    //  - `rest`: The continuation (remaining instruction stream to execute next).
    //  - `ops`: The  operand stack.
    #[val((e: Expr, env: Env, v: Value, rest: IList, ops: VList) -> Lemma(implies(
        eval(e, env) == EvRes::Ok(v),
        exec(app(compile(e), rest), ops, env) == exec(rest, VList::VCons(v, Box::new(ops)), env))))]
    fn compile_correct(e: Expr, env: Env, v: Value, rest: IList, ops: VList) {
        match e {
            Expr::Const(d) => (),
            Expr::Id(x) => (),
            Expr::Add(e1, e2) => (),
            Expr::Sub(e1, e2) => (),
            Expr::Mul(e1, e2) => (),
            Expr::Div(e1, e2) => (),
            Expr::Geq(e1, e2) => (),
            Expr::Gt(e1, e2) => (),
            Expr::Eq(e1, e2) => (),
            Expr::And(e1, e2) => (),
            Expr::Or(e1, e2) => (),
            Expr::Not(e1) => (),
            Expr::IfThenElse(c, t, f) => (),
            Expr::Let(x, e1, e2) => (),
        }
    }
}
