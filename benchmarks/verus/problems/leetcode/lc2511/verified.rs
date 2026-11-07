use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn find_next_nonzero(forts: Seq<i32>, start: nat) -> nat
        recommends start <= forts.len(),
        decreases forts.len() - start,
    {
        if start >= forts.len() {
            start
        } else if forts[start as int] != 0 {
            start
        } else {
            Self::find_next_nonzero(forts, start + 1)
        }
    }

    proof fn lemma_scan_spec_skip(forts: Seq<i32>, i: nat, best: nat, j: nat)
        requires
            i <= j <= forts.len(),
            forall |k: nat| i <= k < j ==> forts[k as int] == 0,
        ensures
            Self::scan_spec(forts, i, best) == Self::scan_spec(forts, j, best),
        decreases j - i,
    {
        if i == j {
        } else {
            assert(forts[i as int] == 0);
            Self::lemma_scan_spec_skip(forts, i + 1, best, j);
        }
    }

    pub open spec fn scan_spec(forts: Seq<i32>, i: nat, best: nat) -> nat
        recommends i <= forts.len(),
        decreases forts.len() - i,
    {
        if i >= forts.len() {
            best
        } else if forts[i as int] == 1 || forts[i as int] == -1 {
            let j = Self::find_next_nonzero(forts, i + 1);
            let new_best = if j < forts.len() && forts[i as int] + forts[j as int] == 0 {
                let count = (j - i - 1) as nat;
                if best < count { count } else { best }
            } else {
                best
            };
            Self::scan_spec(forts, i + 1, new_best)
        } else {
            Self::scan_spec(forts, i + 1, best)
        }
    }

    pub open spec fn capture_forts_spec(forts: Seq<i32>) -> nat {
        Self::scan_spec(forts, 0, 0)
    }

    pub fn capture_forts(forts: Vec<i32>) -> (res: i32)
        requires
            1 <= forts.len() <= 1000,
            forall|i: int| 0 <= i < forts.len() ==>
                (forts[i] == -1 || forts[i] == 0 || forts[i] == 1),
        ensures
            0 <= res,
            res as nat == Self::capture_forts_spec(forts@),
    {
        let mut best: i32 = 0;
        let mut i: usize = 0;

        while i < forts.len()
            invariant
                1 <= forts.len() <= 1000,
                forall|k: int| 0 <= k < forts.len() ==>
                    (forts[k] == -1 || forts[k] == 0 || forts[k] == 1),
                0 <= i <= forts.len(),
                0 <= best as int <= forts@.len() - 1,
                Self::scan_spec(forts@, i as nat, best as nat) == Self::capture_forts_spec(forts@),
            decreases forts.len() - i,
        {
            let ghost old_i_nat: nat = i as nat;
            let ghost old_best_nat: nat = best as nat;

            if forts[i] == 1 || forts[i] == -1 {
                let mut j: usize = i + 1;

                while j < forts.len() && forts[j] == 0
                    invariant
                        1 <= forts.len() <= 1000,
                        forall|k: int| 0 <= k < forts.len() ==>
                            (forts[k] == -1 || forts[k] == 0 || forts[k] == 1),
                        0 <= i < forts.len(),
                        i + 1 <= j <= forts.len(),
                        forall|k: nat| (i + 1) as nat <= k < j as nat ==> forts@[k as int] == 0,
                        Self::find_next_nonzero(forts@, j as nat)
                            == Self::find_next_nonzero(forts@, (i + 1) as nat),
                    decreases forts.len() - j,
                {
                    let ghost old_j_nat: nat = j as nat;
                    j = j + 1;

                    proof {
                        assert(old_j_nat < forts@.len());
                        assert(forts@[old_j_nat as int] == 0);
                        assert(Self::find_next_nonzero(forts@, old_j_nat)
                            == Self::find_next_nonzero(forts@, old_j_nat + 1));
                    }
                }

                proof {
                    if j == forts.len() {
                        assert(Self::find_next_nonzero(forts@, j as nat) == j as nat);
                    } else {
                        assert(!(j < forts.len() && forts@[j as int] == 0));
                        assert(forts@[j as int] != 0);
                        assert(Self::find_next_nonzero(forts@, j as nat) == j as nat);
                    }
                    assert(j as nat == Self::find_next_nonzero(forts@, (i + 1) as nat));
                }

                if j < forts.len() && forts[i] + forts[j] == 0 {
                    let count_usize = j - i - 1;

                    proof {
                        assert(i + 1 <= j);
                        assert(count_usize < forts.len());
                        assert(forts.len() <= 1000);
                        assert(count_usize <= i32::MAX as usize);
                    }

                    let count = count_usize as i32;
                    if count > best {
                        best = count;
                    }

                    proof {
                        let count_nat = (j as nat - old_i_nat - 1) as nat;
                        assert(count_nat == count_usize as nat);
                        assert(count as nat == count_nat);
                        assert(best as nat == if old_best_nat < count_nat { count_nat } else { old_best_nat });
                        assert(count_nat <= forts@.len() - 1);
                        assert(best as int <= forts@.len() - 1);
                    }
                } else {
                    proof {
                        assert(best as nat == old_best_nat);
                        assert(best as int <= forts@.len() - 1);
                    }
                }

                proof {
                    assert(Self::find_next_nonzero(forts@, old_i_nat + 1) == j as nat);
                    assert(forts@[old_i_nat as int] == 1 || forts@[old_i_nat as int] == -1);
                    assert(Self::scan_spec(forts@, old_i_nat, old_best_nat)
                        == Self::scan_spec(forts@, old_i_nat + 1, best as nat));
                    
                    Self::lemma_scan_spec_skip(forts@, old_i_nat + 1, best as nat, j as nat);
                    assert(Self::scan_spec(forts@, old_i_nat + 1, best as nat) == Self::scan_spec(forts@, j as nat, best as nat));
                }
                if j > i + 1 {
                    i = j - 1;
                }
            } else {
                proof {
                    assert(forts@[old_i_nat as int] != 1 && forts@[old_i_nat as int] != -1);
                    assert(best as nat == old_best_nat);
                    assert(Self::scan_spec(forts@, old_i_nat, old_best_nat)
                        == Self::scan_spec(forts@, old_i_nat + 1, best as nat));
                }
            }

            i = i + 1;

            proof {
                assert(Self::scan_spec(forts@, i as nat, best as nat) == Self::capture_forts_spec(forts@)) by {
                    assert(Self::scan_spec(forts@, old_i_nat, old_best_nat) == Self::capture_forts_spec(forts@));
                }
            }
        }

        proof {
            assert(i == forts.len());
            assert(Self::scan_spec(forts@, forts.len() as nat, best as nat) == best as nat);
            assert(best as nat == Self::capture_forts_spec(forts@));
        }

        best
    }
}

} 
