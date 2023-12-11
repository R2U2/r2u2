use egg::*;

define_language! {
    enum Prop {
        Bool(bool),
        Num(i32),
        "G" = Global([Id; 3]),
        "&" = And([Id; 2]),
        "!" = Not(Id),
        "|" = Or([Id; 2]),
        Symbol(Symbol),
    }
}

type EGraph = egg::EGraph<Prop, ConstantFold>;
type Rewrite = egg::Rewrite<Prop, ConstantFold>;

#[derive(Default)]
struct ConstantFold;
impl Analysis<Prop> for ConstantFold {

    // when merging two e-classes, the wpd will be the minimum of the two, bpd will be the max.
    // the only time two e-classes with different delays will merge is in the rewrite rules like:
    //   G[3,5]p || G[0,10]p |-> G[3,5]p

    // (Option<bool>, (u32, u32), (u32, u32), u32            )
    // (const?      , (lb, ub)  , (bpd, wpd), childrens' cost)
    type Data = ((Option<bool>, (u32, u32), (u32, u32), u32), PatternAst<Prop>);
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        DidMerge(true, true)
    }

    fn make(egraph: &EGraph, enode: &Prop) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        let result = match enode {
            Prop::Bool(c) => ((Some(*c), (0,0), (0,0), 1), c.to_string().parse().unwrap()),
            Prop::Num(n) => ((Some(true), (0,0), (0,0), 1), n.to_string().parse().unwrap()),
            Prop::Symbol(s) => ((None, (0,0), (0,0), 1), s.to_string().parse().unwrap()),
            Prop::Global([l, u, a]) => (
                (
                    x(a).0.0, 
                    (x(l).0.1.0, x(u).0.1.1), 
                    (x(a).0.2.0 + x(l).0.1.0, x(a).0.2.1 + x(l).0.1.1), 
                    0
                ),
                format!("(G {} {} {})", x(l).0.1.0, x(u).0.1.1, x(a).1).parse().unwrap(),
            ),
            Prop::And([a, b]) => Some((
                (x(a)?.0 && x(b)?.0, (0,0), (0,0)),
                format!("(& {} {})", x(a)?.0, x(b)?.0).parse().unwrap(),
            )),
            Prop::Not(a) => Some((
                (!x(a)?.0, (0,0), (0,0)), format!("(~ {})", x(a)?.0).parse().unwrap()
            )),
            Prop::Or([a, b]) => Some((
                (x(a)?.0 || x(b)?.0, (0,0), (0,0)),
                format!("(| {} {})", x(a)?.0, x(b)?.0).parse().unwrap(),
            ))
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

rule! {def_imply, def_imply_flip,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg, double_neg_flip,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (~ ?a))",    "true"                      }
rule! {or_true,     "(| ?a true)",         "true"                      }
rule! {and_true,    "(& ?a true)",         "?a"                     }

// this has to be a multipattern since (& (-> ?a ?b) (-> (~ ?a) ?c))  !=  (| ?b ?c)
// see https://github.com/egraphs-good/egg/issues/185
fn lem_imply() -> Rewrite {
    multi_rewrite!(
        "lem_imply";
        "?value = true = (& (-> ?a ?b) (-> (~ ?a) ?c))"
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
    let true_id = runner.egraph.add(Prop::Bool(true));
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
            "(| (~ x) y)",
            "(| (~ x) (~ (~ y)))",
            "(| (~ (~ y)) (~ x))",
            "(-> (~ y) (~ x))",
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
            "(& (-> (~ y) (~ x)) (-> y z))",
            "(& (-> y z)         (-> (~ y) (~ x)))",
            "(| z (~ x))",
            "(| (~ x) z)",
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