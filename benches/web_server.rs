//! Processes a number of web requests using a map as the data store for the "server"
//!
//! This models how the various maps do under a random set of create, read, update, and delete
//! operations.

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
    black_box,
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

    fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;
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

            fn remove<Q>(&mut self, key: &Q) -> Option<V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::remove(self, key)
            }
        }
    };
}

impl_map!(HashMap, Hash + Eq);
impl_map!(BTreeMap, Ord);
impl_map!(SimpleBSTMap, Ord);
impl_map!(BSTMap, Ord);

#[derive(Debug, Clone, PartialEq)]
enum Request {
    /// Create a new entry with the given information
    ///
    /// Produces `Response::Created` if the operation succeeds.
    /// Produces `Error::BadRequest` if the ID already exists.
    Create {
        id: usize,
        entry: Entry,
    },

    /// Get a field from the entry with the given ID
    ///
    /// Produces `Response::Field` with the requested field if the operation succeeds.
    /// Produces `Error::NotFound` if the ID does not exist
    Get {
        id: usize,
        field: Field,
    },

    /// Update a field in the entry with the given ID
    ///
    /// Produces `Response::Field` with the updated field value if the operation succeeds.
    /// Produces `Error::NotFound` if the ID does not exist
    Update {
        id: usize,
        field: FieldValue,
    },

    /// Delete the entry with the given ID
    ///
    /// Produces `Response::Deleted` if the operation succeeds.
    /// Produces `Error::NotFound` if the ID does not exist
    Delete {
        id: usize,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum Response {
    Created {
        id: usize,
    },

    Field {
        id: usize,
        field: FieldValue,
    },

    Deleted {
        id: usize,
        entry: Entry,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Field {
    Name,
    PhoneNumber,
    Email,
}

#[derive(Debug, Clone, PartialEq)]
enum FieldValue {
    Name(Rc<str>),
    PhoneNumber(usize),
    Email(Rc<str>),
}

#[derive(Debug, Clone, PartialEq)]
enum Error {
    NotFound,
    BadRequest,
}

#[derive(Debug, Clone, PartialEq)]
struct Entry {
    pub name: Rc<str>,
    pub phone_number: usize,
    pub email: Rc<str>,
}

#[derive(Debug, Default, Clone)]
struct Counters {
    /// Number of requests that were successfully processed
    pub successes: usize,
    /// Number of requests that produced `Error::NotFound`
    pub not_found: usize,
    /// Number of requests that produced `Error::BadRequest`
    pub bad_requests: usize,
}

#[derive(Debug, Default)]
struct Server<M: Map<usize, Entry>> {
    data: M,
}

impl<M: Map<usize, Entry>> Server<M> {
    pub fn handle(&mut self, req: &Request) -> Result<Response, Error> {
        use Request::*;
        match *req {
            Create {id, ref entry} => {
                // Need to check if the entry exists already because we don't want to overwrite if
                // it does
                if self.data.contains_key(&id) {
                    return Err(Error::BadRequest);
                }

                self.data.insert(id, entry.clone());

                Ok(Response::Created {id})
            },


            Get {id, ref field} => {
                let entry = self.data.get(&id).ok_or(Error::NotFound)?;

                let field = match field {
                    Field::Name => FieldValue::Name(entry.name.clone()),
                    Field::PhoneNumber => FieldValue::PhoneNumber(entry.phone_number),
                    Field::Email => FieldValue::Email(entry.email.clone()),
                };

                Ok(Response::Field {id, field})
            },

            Update {id, ref field} => {
                let entry = self.data.get_mut(&id).ok_or(Error::NotFound)?;

                let field = match *field {
                    FieldValue::Name(ref name) => {
                        entry.name = name.clone();
                        FieldValue::Name(name.clone())
                    },

                    FieldValue::PhoneNumber(phone_number) => {
                        entry.phone_number = phone_number;
                        FieldValue::PhoneNumber(phone_number)
                    },

                    FieldValue::Email(ref email) => {
                        entry.email = email.clone();
                        FieldValue::Email(email.clone())
                    },
                };

                Ok(Response::Field {id, field})
            },

            Delete {id} => {
                let entry = self.data.remove(&id).ok_or(Error::NotFound)?;

                Ok(Response::Deleted {id, entry})
            },
        }
    }
}

fn run_requests<M: Map<usize, Entry>>(requests: &[Request]) -> (Server<M>, Counters) {
    let mut server = Server::<M>::default();

    let mut counters = Counters::default();
    for req in requests {
        match server.handle(req) {
            Ok(response) => {
                black_box(response);
                counters.successes += 1;
            },

            Err(Error::NotFound) => counters.not_found += 1,
            Err(Error::BadRequest) => counters.bad_requests += 1,
        }
    }

    (server, counters)
}

fn generate_requests(reqs: usize) -> Vec<Request> {
    // Use seed to make this deterministic
    let mut rng = StdRng::seed_from_u64(80317189);

    let mut requests = Vec::with_capacity(reqs);

    // The set of IDs that currently exist (and have not been deleted)
    let mut existing_entries = Vec::with_capacity(reqs);

    let mut i = 0;
    while i < reqs {
        match rng.gen_range(1..=100) {
            // Create a new entry
            1..=20 => {
                requests.push(Request::Create {
                    // Since `i` is guaranteed to be unique, this will never produce a bad request
                    id: i,
                    entry: Entry {
                        name: random_str(&mut rng, 16),
                        phone_number: random_phone_number(&mut rng),
                        email: random_str(&mut rng, 38),
                    },
                });

                existing_entries.push(i);
            },

            // Get a field from an existing entry
            21..=60 => {
                let id = match existing_entries.choose(&mut rng).copied() {
                    Some(id) => id,
                    // No entries currently, so can't generate this type of request yet
                    None => continue,
                };

                requests.push(Request::Get {
                    id,
                    field: match rng.gen_range(1..=3) {
                        1 => Field::Name,
                        2 => Field::PhoneNumber,
                        3 => Field::Email,
                        _ => unreachable!(),
                    },
                });
            },

            // Update a field in an existing entry
            61..=90 => {
                let id = match existing_entries.choose(&mut rng).copied() {
                    Some(id) => id,
                    // No entries currently, so can't generate this type of request yet
                    None => continue,
                };

                requests.push(Request::Update {
                    id,
                    field: match rng.gen_range(1..=3) {
                        1 => FieldValue::Name(random_str(&mut rng, 16)),
                        2 => FieldValue::PhoneNumber(random_phone_number(&mut rng)),
                        3 => FieldValue::Email(random_str(&mut rng, 38)),
                        _ => unreachable!(),
                    },
                });
            },

            // Delete an existing entry
            91..=100 => {
                let id = match existing_entries.choose(&mut rng).copied() {
                    Some(id) => id,
                    // No entries currently, so can't generate this type of request yet
                    None => continue,
                };

                requests.push(Request::Delete {id});

                let entry_index = existing_entries.iter()
                    .position(|&x| x == id)
                    .unwrap();
                existing_entries.remove(entry_index);
            },

            _ => unreachable!(),
        }

        i += 1;
    }

    requests
}

fn random_str(rng: &mut StdRng, len: usize) -> Rc<str> {
    // Not a huge issue if the name is duplicated (unlikely)
    let string: String = iter::repeat_with(|| rng.sample(Alphanumeric))
        .map(char::from)
        .take(len)
        .collect();
    string.into()
}

fn random_phone_number(rng: &mut StdRng) -> usize {
    // Random 10 digit number
    rng.gen_range(1_000_000_000..=9_999_999_999)
}

pub fn bench_web_server(c: &mut Criterion) {
    const REQS: &[usize] = &[500, 1000, 2000, 4000, 10000];

    #[inline(always)]
    fn bench<M: Map<usize, Entry>>(
        name: &'static str,
        group: &mut BenchmarkGroup<WallTime>,
        requests: &usize,
    ) {
        group.bench_with_input(BenchmarkId::new(name, requests), requests, |b, &requests| {
            let reqs = generate_requests(requests);
            b.iter(|| run_requests::<M>(&reqs))
        });
    }

    let mut group = c.benchmark_group("map web server");
    for requests in REQS {
        bench::<HashMap<usize, Entry>>("HashMap", &mut group, requests);
        bench::<BTreeMap<usize, Entry>>("BTreeMap", &mut group, requests);
        bench::<SimpleBSTMap<usize, Entry>>("SimpleBSTMap", &mut group, requests);
        bench::<BSTMap<usize, Entry>>("BSTMap", &mut group, requests);
    }
    group.finish();
}

criterion_group!(benches,
    bench_web_server,
);

criterion_main!(benches);
