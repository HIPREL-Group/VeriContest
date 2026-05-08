use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_minimum_capacity_index(capacity: Seq<i32>, item_size: i32, idx: int) -> bool {
        0 <= idx < capacity.len()
            && capacity[idx] >= item_size
            && forall |j: int| 0 <= j < capacity.len() && capacity[j] >= item_size ==> capacity[idx] <= #[trigger] capacity[j]
            && forall |j: int| 0 <= j < capacity.len() && capacity[j] >= item_size && capacity[j] == capacity[idx] ==> idx <= j
    }

    pub open spec fn valid_result(capacity: Seq<i32>, item_size: i32, res: int) -> bool {
        (res == -1 && forall |j: int| 0 <= j < capacity.len() ==> #[trigger] capacity[j] < item_size)
            || (0 <= res && Self::is_minimum_capacity_index(capacity, item_size, res))
    }

    pub fn minimum_index(capacity: Vec<i32>, item_size: i32) -> (res: i32)
        requires
            1 <= capacity.len() <= 100,
            forall |k: int| 0 <= k < capacity.len() ==> 1 <= #[trigger] capacity[k] <= 100,
            1 <= item_size <= 100,
        ensures
            Self::valid_result(capacity@, item_size, res as int),
    {
        let n = capacity.len();
        let mut i: usize = 0;
        let mut found: bool = false;
        let mut best_idx: usize = 0;
        let mut best_cap: i32 = 0;

        while i < n
            invariant
                n == capacity.len(),
                1 <= n <= 100,
                1 <= item_size <= 100,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] capacity[k] <= 100,
                0 <= i <= n,
                !found ==> forall |j: int| 0 <= j < i ==> #[trigger] capacity[j] < item_size,
                found ==> 0 <= best_idx < i,
                found ==> best_cap == capacity[best_idx as int],
                found ==> capacity[best_idx as int] >= item_size,
                found ==> forall |j: int| 0 <= j < i && capacity[j] >= item_size ==> best_cap <= #[trigger] capacity[j],
                found ==> forall |j: int| 0 <= j < i && capacity[j] >= item_size && capacity[j] == best_cap ==> best_idx as int <= j,
            decreases n - i,
        {
            let cap_i = capacity[i];
            if cap_i >= item_size {
                if !found {
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;

                    proof {
                        assert(best_idx as int == i as int);
                        assert(best_cap == capacity[i as int]);
                        assert(best_cap >= item_size);

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size implies best_cap <= #[trigger] capacity[j] by {
                            if j == i as int {
                            } else {
                                assert(0 <= j < i);
                                assert(capacity[j] < item_size);
                                assert(false);
                            }
                        }

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size && capacity[j] == best_cap implies best_idx as int <= j by {
                            if j == i as int {
                            } else {
                                assert(0 <= j < i);
                                assert(capacity[j] < item_size);
                                assert(capacity[j] >= item_size);
                                assert(false);
                            }
                        }
                    }
                } else if cap_i < best_cap {
                    let ghost old_best_cap = best_cap;
                    found = true;
                    best_idx = i;
                    best_cap = cap_i;

                    proof {
                        assert(best_idx as int == i as int);
                        assert(best_cap == capacity[i as int]);
                        assert(best_cap >= item_size);

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size implies best_cap <= #[trigger] capacity[j] by {
                            if j == i as int {
                            } else {
                                assert(0 <= j < i);
                                assert(old_best_cap <= capacity[j]);
                                assert(cap_i < old_best_cap);
                            }
                        }

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size && capacity[j] == best_cap implies best_idx as int <= j by {
                            if j == i as int {
                            } else {
                                assert(0 <= j < i);
                                assert(old_best_cap <= capacity[j]);
                                assert(capacity[j] == best_cap);
                                assert(best_cap == cap_i);
                                assert(cap_i < old_best_cap);
                                assert(capacity[j] < old_best_cap);
                                assert(false);
                            }
                        }
                    }
                } else {
                    proof {
                        assert(found);
                        assert(cap_i >= best_cap);
                        assert(best_idx < i);

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size implies best_cap <= #[trigger] capacity[j] by {
                            if j == i as int {
                                assert(capacity[j] == cap_i);
                            } else {
                                assert(0 <= j < i);
                            }
                        }

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size && capacity[j] == best_cap implies best_idx as int <= j by {
                            if j == i as int {
                                assert(cap_i == best_cap);
                            } else {
                                assert(0 <= j < i);
                            }
                        }
                    }
                }
            } else {
                proof {
                    if !found {
                        assert forall |j: int| 0 <= j < i as int + 1 implies #[trigger] capacity[j] < item_size by {
                            if j == i as int {
                                assert(capacity[j] == cap_i);
                            } else {
                                assert(0 <= j < i);
                            }
                        }
                    } else {
                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size implies best_cap <= #[trigger] capacity[j] by {
                            if j == i as int {
                                assert(capacity[j] == cap_i);
                                assert(cap_i < item_size);
                                assert(capacity[j] >= item_size);
                                assert(false);
                            } else {
                                assert(0 <= j < i);
                            }
                        }

                        assert forall |j: int| 0 <= j < i as int + 1 && capacity[j] >= item_size && capacity[j] == best_cap implies best_idx as int <= j by {
                            if j == i as int {
                                assert(capacity[j] == cap_i);
                                assert(cap_i < item_size);
                                assert(capacity[j] >= item_size);
                                assert(false);
                            } else {
                                assert(0 <= j < i);
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }

        if found {
            proof {
                assert(i == n);
                assert(0 <= best_idx < n);
                assert(capacity[best_idx as int] >= item_size);
                assert(forall |j: int| 0 <= j < n && capacity[j] >= item_size ==> best_cap <= #[trigger] capacity[j]);
                assert(best_cap == capacity[best_idx as int]);
                assert(forall |j: int| 0 <= j < n && capacity[j] >= item_size && capacity[j] == capacity[best_idx as int] ==> best_idx as int <= j);
                assert(Self::is_minimum_capacity_index(capacity@, item_size, best_idx as int));
                assert(Self::valid_result(capacity@, item_size, best_idx as int));
            }
            best_idx as i32
        } else {
            proof {
                assert(i == n);
                assert(forall |j: int| 0 <= j < n ==> #[trigger] capacity[j] < item_size);
                assert(Self::valid_result(capacity@, item_size, -1));
            }
            -1
        }
    }
}

}
