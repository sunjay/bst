//! Compilers are famously heavy users of map-like data structures. This benchmark is a simplified
//! algorithm for "name resolution" in a very simple language with only function declarations and
//! function calls.

use std::iter;
use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;
use std::cmp;
use std::collections::BTreeMap;

use rand::prelude::*;
use rand::seq::SliceRandom;
use rand::distributions::Alphanumeric;
use criterion::{
    BenchmarkGroup,
    BenchmarkId,
    Criterion,
    criterion_group,
    criterion_main,
    measurement::WallTime,
};
use simple_bst::SimpleBSTMap;
use fnv::FnvHashMap as HashMap;

use bst::BSTMap;

trait Map<K, V>: Default {
    fn get<Q>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

macro_rules! impl_map {
    ($name:ident, $bound:ident $(+ $other_bound:ident)*) => {
        impl<K: Clone, V: Clone> Map<K, V> for $name<K, V>
            where K: $bound $(+ $other_bound)*,
        {
            fn get<Q>(&self, key: &Q) -> Option<&V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get(self, key)
            }

            fn insert(&mut self, key: K, value: V) -> Option<V> {
                $name::insert(self, key, value)
            }
        }
    };
}

impl_map!(HashMap, Hash + Eq);
impl_map!(BTreeMap, Ord);
impl_map!(SimpleBSTMap, Ord);
impl_map!(BSTMap, Ord);

#[derive(Debug, Default)]
struct Counters {
    // The number of valid calls (resolved name + correct number of args)
    valid_calls: usize,
    // The number of unresolved names
    unresolved: usize,
    // The number of times we saw incorrect number of arguments
    incorrect_num_args: usize,
}

fn resolve_program<M: Map<Rc<str>, usize>>(program: &Block) -> Counters {
    let mut counters = Counters::default();

    let mut scope_stack = Vec::new();
    resolve_block::<M>(program, &mut scope_stack, &mut counters);

    counters
}

fn resolve_block<M: Map<Rc<str>, usize>>(
    block: &Block,
    scope_stack: &mut Vec<M>,
    counters: &mut Counters,
) {
    scope_stack.push(M::default());

    'stmtloop:
    for stmt in &block.stmts {
        use Stmt::*;
        match stmt {
            FuncDecl {name, params} => {
                let top_scope = scope_stack.last_mut().unwrap();
                top_scope.insert(Rc::clone(name), *params);
            },

            &Call {ref name, args} => {
                for scope in scope_stack.iter().rev() {
                    if let Some(&params) = scope.get(name) {
                        if args == params {
                            counters.valid_calls += 1;
                        } else {
                            counters.incorrect_num_args += 1;
                        }

                        continue 'stmtloop;
                    }
                }

                // Name was not found
                counters.unresolved += 1;
            },

            Block(block) => resolve_block(block, scope_stack, counters),
        }
    }

    scope_stack.pop().unwrap();
}

#[derive(Debug, Default)]
struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug)]
enum Stmt {
    /// A declaration of a new function in the current scope and its number of
    /// parameters
    ///
    /// Names are allowed to be shadowed.
    FuncDecl {name: Rc<str>, params: usize},

    /// A function call and the number of arguments passed to it
    ///
    /// A name is considered "resolved" if it was declared in the current scope
    /// or any upper scope before use. It is considered "unresolved" otherwise.
    ///
    /// The number of arguments must match the number of parameters declared for
    /// the function.
    Call {name: Rc<str>, args: usize},

    /// A sub-block with more declarations and calls. All of the names declared
    /// in this block are private to this block and no longer visible after this
    /// block.
    Block(Block),
}

/// Generates a random program with `max_stmts` statements and a nesting depth up to `max_depth`.
fn generate_program(max_stmts: usize, max_depth: usize) -> Block {
    // Use seed to make this deterministic
    let mut rng = StdRng::seed_from_u64(9381938492);

    const NAMES_PER_DEPTH_LEVEL: usize = 5;
    let names = generate_names(&mut rng, max_depth, NAMES_PER_DEPTH_LEVEL);

    let mut remaining_stmts = max_stmts;
    let mut program = Block::default();
    while remaining_stmts > 0 {
        let block = generate_block(&mut rng, &names, 0, &mut remaining_stmts, max_depth);
        program.stmts.extend(block.stmts);
    }

    program
}

/// Pre-generates names for each level of depth
fn generate_names(rng: &mut StdRng, max_depth: usize, max_names: usize) -> Vec<Vec<Rc<str>>> {
    let mut names = vec![Vec::new(); max_depth+1];

    for name_list in &mut names {
        for _ in 0..max_names {
            // Not a huge issue if the name is duplicated (unlikely)
            let name: String = iter::repeat_with(|| rng.sample(Alphanumeric))
                .map(char::from)
                .take(8)
                .collect();
            name_list.push(name.into());
        }
    }

    names
}

fn generate_block(
    rng: &mut StdRng,
    names: &[Vec<Rc<str>>],
    current_level: usize,
    remaining_stmts: &mut usize,
    max_depth: usize,
) -> Block {
    const MAX_STMTS_PER_BLOCK: usize = 15;
    const MIN_STMTS_PER_BLOCK: usize = 3;

    let max_stmts = cmp::min(*remaining_stmts, MAX_STMTS_PER_BLOCK);
    let nstmts = if max_stmts >= MIN_STMTS_PER_BLOCK {
        rng.gen_range(MIN_STMTS_PER_BLOCK..=max_stmts)
    } else {
        // use up the remaining statements if we don't have enough for the
        // minimum number of statements
        max_stmts
    };

    let mut stmts = Vec::new();
    for _ in 0..nstmts {
        if *remaining_stmts == 0 {
            break;
        }

        match rng.gen_range(1..=100) {
            // Generate a function decl
            1..=30 => {
                // Pick a name from the current level of depth
                let name = Rc::clone(names[current_level].choose(rng).unwrap());
                let params = rng.gen_range(0..=3);

                stmts.push(Stmt::FuncDecl {name, params});
                *remaining_stmts -= 1;
            },

            // Generate a function call
            31..=80 => {
                // Pick a name from the current scope or an upper scope
                // (name may or may not be declared)
                let name = Rc::clone(names[..=current_level]
                    .choose(rng)
                    .unwrap()
                    .choose(rng)
                    .unwrap());
                let args = rng.gen_range(0..=3);

                stmts.push(Stmt::Call {name, args});
                *remaining_stmts -= 1;
            },

            // Generate a block if we still have depth
            81..=100 => if max_depth > 0 {
                // Count this statement before we recurse
                *remaining_stmts -= 1;
                stmts.push(Stmt::Block(generate_block(
                    rng,
                    names,
                    current_level+1,
                    remaining_stmts,
                    max_depth-1,
                )));
            } else {
                continue;
            },

            _ => unreachable!(),
        }
    }

    Block {stmts}
}

pub fn bench_name_resolution(c: &mut Criterion) {
    const STMTS: &[usize] = &[500, 1000, 2000, 4000, 10000];
    const MAX_DEPTH: usize = 5;

    #[inline(always)]
    fn bench<M: Map<Rc<str>, usize>>(
        name: &'static str,
        group: &mut BenchmarkGroup<WallTime>,
        stmts: &usize,
    ) {
        group.bench_with_input(BenchmarkId::new(name, stmts), stmts, |b, &stmts| {
            let program = generate_program(stmts, MAX_DEPTH);
            b.iter(|| resolve_program::<M>(&program))
        });
    }

    let mut group = c.benchmark_group("map name resolution");
    for stmts in STMTS {
        bench::<HashMap<Rc<str>, usize>>("HashMap", &mut group, stmts);
        bench::<BTreeMap<Rc<str>, usize>>("BTreeMap", &mut group, stmts);
        bench::<SimpleBSTMap<Rc<str>, usize>>("SimpleBSTMap", &mut group, stmts);
        bench::<BSTMap<Rc<str>, usize>>("BSTMap", &mut group, stmts);
    }
    group.finish();
}

criterion_group!(benches,
    bench_name_resolution,
);

criterion_main!(benches);
