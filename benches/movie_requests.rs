//! Given a list of movie requests (movie title, genre), tabulate the votes to see which movie
//! titles were requested the most and which genres were requested the most.

use std::iter;
use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;
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

    fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn contains_key<Q>(&self, key: &Q) -> bool
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

            fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get_mut(self, key)
            }

            fn contains_key<Q>(&self, key: &Q) -> bool
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::contains_key(self, key)
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

struct MovieRequest {
    pub title: Rc<str>,
    pub genre: Rc<str>,
}

#[derive(Default)]
struct Counters<M: Map<Rc<str>, usize>> {
    pub titles: M,
    pub genres: M,
}

/// Tabulates the results of counting the movie titles and genres requested in each request
fn tabulate_requests<M: Map<Rc<str>, usize>>(reqs: &[MovieRequest]) -> Counters<M> {
    let mut counters = Counters::default();

    for request in reqs {
        let MovieRequest {title, genre} = request;

        increment_counter(&mut counters.titles, title);
        increment_counter(&mut counters.genres, genre);
    }

    counters
}

fn increment_counter<M: Map<Rc<str>, usize>>(map: &mut M, name: &Rc<str>) {
    match map.get_mut(name) {
        Some(counter) => *counter += 1,

        None => {
            map.insert(name.clone(), 1);
        },
    }
}

fn generate_requests(requests: usize) -> Vec<MovieRequest> {
    let mut reqs = Vec::with_capacity(requests);

    // Use seed to make this deterministic
    let mut rng = StdRng::seed_from_u64(38718232);

    let titles = generate_names(&mut rng, 25);
    let genres = generate_names(&mut rng, 8);

    for _ in 0..requests {
        reqs.push(MovieRequest {
            title: titles.choose(&mut rng).unwrap().clone(),
            genre: genres.choose(&mut rng).unwrap().clone(),
        });
    }

    reqs
}

/// Pre-generates a list of names of the given length
fn generate_names(rng: &mut StdRng, len: usize) -> Vec<Rc<str>> {
    let mut names = Vec::with_capacity(len);

    for _ in 0..len {
        // Not a huge issue if the name is duplicated (unlikely)
        let name: String = iter::repeat_with(|| rng.sample(Alphanumeric))
            .map(char::from)
            .take(8)
            .collect();
        names.push(name.into());
    }

    names
}

pub fn bench_movie_requests(c: &mut Criterion) {
    const REQS: &[usize] = &[500, 1000, 2000, 4000, 10000];

    #[inline(always)]
    fn bench<M: Map<Rc<str>, usize>>(
        name: &'static str,
        group: &mut BenchmarkGroup<WallTime>,
        requests: &usize,
    ) {
        group.bench_with_input(BenchmarkId::new(name, requests), requests, |b, &requests| {
            let reqs = generate_requests(requests);
            b.iter(|| tabulate_requests::<M>(&reqs))
        });
    }

    let mut group = c.benchmark_group("map movie requests");
    for requests in REQS {
        bench::<HashMap<Rc<str>, usize>>("HashMap", &mut group, requests);
        bench::<BTreeMap<Rc<str>, usize>>("BTreeMap", &mut group, requests);
        bench::<SimpleBSTMap<Rc<str>, usize>>("SimpleBSTMap", &mut group, requests);
        bench::<BSTMap<Rc<str>, usize>>("BSTMap", &mut group, requests);
    }
    group.finish();
}

criterion_group!(benches,
    bench_movie_requests,
);

criterion_main!(benches);
