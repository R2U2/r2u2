use std::cmp;
use std::fmt;
use std::str::FromStr;
use egg::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Interval {
    lb: u32,
    ub: u32
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write strictly the first element into the supplied output
        // stream: `f`. Returns `fmt::Result` which indicates whether the
        // operation succeeded or failed. Note that `write!` uses syntax which
        // is very similar to `println!`.
        write!(f, "({}, {})", self.lb, self.ub)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct IntervalError;

impl FromStr for Interval {
    type Err = IntervalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (lb, ub) = s
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .and_then(|s| s.split_once(','))
            .ok_or(IntervalError)?;

        let lb_fromstr = lb.parse::<u32>().map_err(|_| IntervalError)?;
        let ub_fromstr = ub.parse::<u32>().map_err(|_| IntervalError)?;

        Ok(Interval { lb: lb_fromstr, ub: ub_fromstr })
    }
}

define_language! {
    enum MLTL {
        Bool(bool),
        Interval(Interval),
        "G" = Global([Id; 2]),
        "&2" = And2([Id; 2]),
        "&3" = And3([Id; 3]),
        "!" = Not(Id),
        Symbol(Symbol),
    }
}

type EGraph = egg::EGraph<MLTL, ConstantFold>;
type Rewrite = egg::Rewrite<MLTL, ConstantFold>;

#[derive(Debug, Clone)]
struct Meta {
    const_match: Option<(bool, PatternAst<MLTL>)>,
    interval: Option<Interval>,
    bpd: u32,
    wpd: u32,
    cost: u32
}

#[derive(Default)]
struct ConstantFold;
impl Analysis<MLTL> for ConstantFold {

    // when merging two e-classes, the wpd will be the minimum of the two, bpd will be the max.
    // the only time two e-classes with different delays will merge is in the rewrite rules like:
    //   G[3,5]p || G[0,10]p |-> G[3,5]p

    // (Option<bool>, (u32, u32), (u32, u32), u32            )
    // (const?      , (lb, ub)  , (bpd, wpd), childrens' cost)
    type Data = Meta;


    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        DidMerge(true, true)
    }

    fn make(egraph: &EGraph, enode: &MLTL) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;

        let result = match enode {
            MLTL::Bool(c) => Self::Data { 
                const_match: Some((*c, c.to_string().parse().unwrap())), 
                interval: None, 
                bpd: 0, 
                wpd: 0, 
                cost: 1 
            },
            MLTL::Interval(i) => Self::Data { 
                const_match: None, 
                interval: Some(*i), 
                bpd: 0, 
                wpd: 0, 
                cost: 0 
            },
            MLTL::Symbol(s) => Self::Data { 
                const_match: None, 
                interval: None, 
                bpd: 0, 
                wpd: 0, 
                cost: 1 
            },
            MLTL::Global([i, a]) => Self::Data { 
                const_match: None, 
                interval: None, 
                bpd: x(a).bpd + x(i).interval.unwrap_or(Interval { lb: 0, ub: 0 }).lb,
                wpd: x(a).wpd + x(i).interval.unwrap_or(Interval { lb: 0, ub: 0 }).ub,
                cost: x(a).cost + 1
            },
            MLTL::And2([a, b]) => {
                let min_bpd_cls = cmp::min(x(a).bpd, x(b).bpd);
                Self::Data { 
                    const_match: None, 
                    interval: None, 
                    bpd: cmp::min(x(a).bpd, x(b).bpd), 
                    wpd: cmp::max(x(a).wpd, x(b).wpd), 
                    cost: 0
                }
            },
            MLTL::And3([a, b, c]) => Self::Data { 
                const_match: None, 
                interval: None, 
                bpd: cmp::min(x(a).bpd, cmp::min(x(b).bpd, x(c).bpd)), 
                wpd: cmp::max(x(a).wpd, cmp::max(x(b).wpd, x(c).wpd)), 
                cost: 1 
            },
            MLTL::Not(a) => Self::Data { 
                const_match: None, 
                interval: None, 
                bpd: x(a).bpd, 
                wpd: x(a).wpd, 
                cost: x(a).cost + 1
            }
        };
        println!("Make: {:?} -> {:?}", enode, result);
        result
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
            egraph.union_instantiations(
                &c.1,
                &c.0.0.to_string().parse().unwrap(),
                &Default::default(),
                "analysis".to_string(),
            );
        }
    }
}

macro_rules! rule {
    ($name:ident, $left:literal, $right:literal) => {
        #[allow(dead_code)]
        fn $name() -> Rewrite {
            rewrite!(stringify!($name); $left => $right)
        }
    };
    ($name:ident, $name2:ident, $left:literal, $right:literal) => {
        rule!($name, $left, $right);
        rule!($name2, $right, $left);
    };
}

rule! {def_imply, def_imply_flip,   "(-> ?a ?b)",       "(| (! ?a) ?b)"          }
rule! {double_neg, double_neg_flip,  "(! (! ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (! ?a))",    "true"                      }
rule! {or_true,     "(| ?a true)",         "true"                      }
rule! {and_true,    "(& ?a true)",         "?a"                     }

// this has to be a multipattern since (& (-> ?a ?b) (-> (! ?a) ?c))  !=  (| ?b ?c)
// see https://github.com/egraphs-good/egg/issues/185
fn lem_imply() -> Rewrite {
    multi_rewrite!(
        "lem_imply";
        "?value = true = (& (-> ?a ?b) (-> (! ?a) ?c))"
        =>
        "?value = (| ?b ?c)"
    )
}

fn prove_something(name: &str, start: &str, rewrites: &[Rewrite], goals: &[&str]) {
    // let _ = env_logger::builder().is_test(true).try_init();
    println!("Proving {}", name);

    let start_expr: RecExpr<_> = start.parse().unwrap();
    let goal_exprs: Vec<RecExpr<_>> = goals.iter().map(|g| g.parse().unwrap()).collect();

    let mut runner = Runner::default()
        .with_iter_limit(20)
        .with_node_limit(5_000)
        .with_expr(&start_expr);

    // we are assume the input expr is true
    // this is needed for the soundness of lem_imply
    let true_id = runner.egraph.add(MLTL::Bool(true));
    let root = runner.roots[0];
    runner.egraph.union(root, true_id);
    runner.egraph.rebuild();

    let egraph = runner.run(rewrites).egraph;

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        println!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn prove_contrapositive() {
    // let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[def_imply(), def_imply_flip(), double_neg_flip(), comm_or()];
    prove_something(
        "contrapositive",
        "(-> x y)",
        rules,
        &[
            "(-> x y)",
            "(| (! x) y)",
            "(| (! x) (! (! y)))",
            "(| (! (! y)) (! x))",
            "(-> (! y) (! x))",
        ],
    );
}

#[test]
fn prove_chain() {
    // let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[
        // rules needed for contrapositive
        def_imply(),
        def_imply_flip(),
        double_neg_flip(),
        comm_or(),
        // and some others
        comm_and(),
        lem_imply(),
    ];
    prove_something(
        "chain",
        "(& (-> x y) (-> y z))",
        rules,
        &[
            "(& (-> x y) (-> y z))",
            "(& (-> (! y) (! x)) (-> y z))",
            "(& (-> y z)         (-> (! y) (! x)))",
            "(| z (! x))",
            "(| (! x) z)",
            "(-> x z)",
        ],
    );
}

fn main() {
    let start = "(| (& false true) (& (G 0 5 true) false))";
    let start_expr = start.parse().unwrap();
    let end = "false";
    let end_expr = end.parse().unwrap();
    let mut eg = EGraph::default();
    eg.add_expr(&start_expr);
    eg.rebuild();
    assert!(!eg.equivs(&start_expr, &end_expr).is_empty());
}