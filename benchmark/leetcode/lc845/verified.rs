use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_subarray(s: Seq<i32>, l: int, r: int, peak: int) -> bool {
        0 <= l && l < peak && peak < r && r < s.len()
        && (forall |a: int, b: int| l <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b <= r ==> s[a] > s[b])
    }

    pub fn longest_mountain(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
        ensures
            result >= 0,
            result > 0 ==> (exists |l: int, r: int, peak: int|
                #[trigger] Self::is_mountain_subarray(arr@, l, r, peak)
                && r - l + 1 == result as int),
            result == 0 ==> (forall |l: int, r: int, peak: int|
                !Self::is_mountain_subarray(arr@, l, r, peak)),
            forall |l: int, r: int, peak: int|
                #[trigger] Self::is_mountain_subarray(arr@, l, r, peak)
                ==> r - l + 1 <= result as int,
    {
        let n = arr.len();
        if n < 3 {
            proof {
                assert forall |l: int, r: int, peak: int|
                    !Self::is_mountain_subarray(arr@, l, r, peak) by {};
            }
            return 0;
        }

        let mut best: i32 = 0;
        let ghost mut best_l: int = 0;
        let ghost mut best_r: int = 0;
        let ghost mut best_peak: int = 0;
        let mut up: usize = 0;
        let mut down: usize = 0;
        let mut i: usize = 1;
        
        let ghost mut last_plateau: usize = 0;

        while i < n
            invariant
                1 <= i <= n,
                n == arr.len(),
                n >= 3,
                1 <= n <= 10_000,
                best >= 0,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] arr[k] <= 10_000,
                up + down < i,
                up <= i - 1,
                
                up > 0 ==> (
                    forall |a: int, b: int|
                        i as int - 1 - up as int - down as int <= a < b <= i as int - 1 - down as int
                        ==> arr@[a] < arr@[b]
                ),
                
                down > 0 ==> up > 0,
                down > 0 ==> (
                    forall |a: int, b: int|
                        i as int - 1 - down as int <= a < b <= i as int - 1
                        ==> arr@[a] > arr@[b]
                ),
                up == 0 ==> down == 0,
                
                up > 0 ==> (
                    i as int - 1 - up as int - down as int == 0
                    || arr@[i as int - 1 - up as int - down as int - 1] >= arr@[i as int - 1 - up as int - down as int]
                ),
                
                (last_plateau as int) < (i as int),
                up == 0 ==> (
                    last_plateau == 0
                    || arr@[last_plateau as int - 1] == arr@[last_plateau as int]
                ),
                up == 0 ==> (
                    forall |m: int| (last_plateau as int) < m && m < (i as int) ==> #[trigger] arr@[m] < arr@[m - 1]
                ),
                
                best > 0 ==> (
                    Self::is_mountain_subarray(arr@, best_l, best_r, best_peak)
                    && best_r - best_l + 1 == best as int
                ),
                
                forall |l: int, r: int, peak: int|
                    #[trigger] Self::is_mountain_subarray(arr@, l, r, peak) && r < i as int
                    ==> r - l + 1 <= best as int,
            decreases n - i,
        {
            if arr[i] > arr[i - 1] {
                if down > 0 {
                    proof {
                        
                        
                        assert(arr@[i as int - 1] < arr@[i as int]);
                        
                        assert(arr@[i as int - 2] > arr@[i as int - 1]);
                    }
                    up = 0;
                    down = 0;
                }
                up = up + 1;
            } else if arr[i] < arr[i - 1] {
                if up > 0 {
                    proof {
                        
                        assert forall |a: int, b: int|
                            i as int - 1 - down as int <= a < b <= i as int
                            implies arr@[a] > arr@[b] by {
                            if b == i as int {
                                if a < i as int - 1 {
                                    assert(arr@[a] > arr@[i as int - 1]);
                                }
                                assert(arr@[i as int - 1] > arr@[i as int]);
                            }
                        };
                    }
                    down = down + 1;
                }
                
            } else {
                
                proof { last_plateau = i; }
                up = 0;
                down = 0;
            }

            if up > 0 && down > 0 {
                let len = (up + down + 1) as i32;
                if len > best {
                    proof {
                        let peak: int = i as int - down as int;
                        let l: int = peak - up as int;
                        let r: int = i as int;
                        assert(Self::is_mountain_subarray(arr@, l, r, peak));
                        best_peak = peak;
                        best_l = l;
                        best_r = r;
                    }
                    best = len;
                }
            }

            proof {
                
                
                let i_val: int = i as int;
                let P: int = i_val - down as int;   
                let L: int = P - up as int;          

                assert forall |l: int, r: int, peak: int|
                    Self::is_mountain_subarray(arr@, l, r, peak) && r == i_val
                    implies r - l + 1 <= best as int by {

                    
                    

                    if up == 0 {
                        
                        
                        if peak > last_plateau as int {
                            
                            
                            assert(arr@[peak - 1] > arr@[peak]);
                            
                            assert(arr@[peak - 1] < arr@[peak]);
                            assert(false);
                        } else if peak == last_plateau as int {
                            if last_plateau > 0 {
                                
                                assert(arr@[peak - 1] == arr@[peak]);
                                
                                assert(arr@[peak - 1] < arr@[peak]);
                                assert(false);
                            } else {
                                
                                assert(0 <= l);
                                assert(l < peak);
                                assert(peak == 0 as int);
                                assert(false);
                            }
                        } else {
                            
                            if last_plateau > 0 {
                                
                                assert(arr@[last_plateau as int - 1] == arr@[last_plateau as int]);
                                
                                
                                assert(arr@[last_plateau as int - 1] > arr@[last_plateau as int]);
                                assert(false);
                            } else {
                                
                                assert(0 <= l);
                                assert(l < peak);
                                assert((last_plateau as int) == 0);
                                assert(peak < 0 as int);
                                assert(false);
                            }
                        }
                    } else if down == 0 {
                        
                        
                        
                        
                        
                        assert(arr@[i_val - 1] < arr@[i_val]) by {
                            
                            
                            
                            
                            assert forall |a: int, b: int|
                                (i_val - up as int) <= a < b <= i_val
                                implies arr@[a] < arr@[b] by {
                                if b == i_val {
                                    if a == i_val - 1 {
                                        
                                        assert(arr@[i_val - 1] < arr@[i_val]);
                                    } else {
                                        
                                        
                                        
                                        
                                        
                                        
                                        assert(arr@[a] < arr@[i_val - 1]);
                                        assert(arr@[i_val - 1] < arr@[i_val]);
                                    }
                                }
                                
                                
                            };
                        };
                        
                        assert(arr@[i_val - 1] > arr@[i_val]);
                        assert(false);
                    } else {
                        
                        

                        
                        if peak != P {
                            if peak > P {
                                
                                assert(arr@[P] > arr@[P + 1]);
                                if l <= P {
                                    
                                    assert(arr@[P] < arr@[P + 1]);
                                } else {
                                    
                                    
                                    assert(arr@[l] > arr@[l + 1]);
                                    
                                    assert(arr@[l] < arr@[l + 1]);
                                }
                                assert(false);
                            } else {
                                
                                assert(arr@[P - 1] < arr@[P]);
                                
                                assert(arr@[P - 1] > arr@[P]);
                                assert(false);
                            }
                        }

                        
                        if l < L {
                            
                            assert(L > 0 as int);
                            
                            assert(arr@[L - 1] >= arr@[L]);
                            
                            assert(arr@[L - 1] < arr@[L]);
                            assert(false);
                        }

                        
                        assert(r - l + 1 <= up as int + down as int + 1);
                        
                        assert(best as int >= up as int + down as int + 1);
                    }
                };
            }

            i = i + 1;
        }

        proof {
            
            assert forall |l: int, r: int, peak: int|
                #[trigger] Self::is_mountain_subarray(arr@, l, r, peak)
                implies r - l + 1 <= best as int by {
                
                assert(r < n as int);
            };
            
            assert(best == 0 ==> forall |l: int, r: int, peak: int|
                !Self::is_mountain_subarray(arr@, l, r, peak)) by {
                if best == 0 {
                    assert forall |l: int, r: int, peak: int|
                        !Self::is_mountain_subarray(arr@, l, r, peak) by {
                        if Self::is_mountain_subarray(arr@, l, r, peak) {
                            assert(r - l + 1 <= 0 as int);
                            assert(l < peak); assert(peak < r);
                            assert(r - l + 1 >= 3 as int);
                            assert(false);
                        }
                    };
                }
            };
        }

        best
    }
}

}
