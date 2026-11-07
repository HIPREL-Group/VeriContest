use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn passes_filter(
    restaurants: Seq<Vec<i32>>,
    i: int,
    vegan_friendly: i32,
    max_price: i32,
    max_distance: i32,
) -> bool {
    &&& (vegan_friendly == 0 || restaurants[i][2] == 1)
    &&& restaurants[i][3] <= max_price
    &&& restaurants[i][4] <= max_distance
}

pub open spec fn ranked_higher(
    restaurants: Seq<Vec<i32>>,
    a: int,
    b: int,
) -> bool {
    restaurants[a][1] > restaurants[b][1]
    || (restaurants[a][1] == restaurants[b][1] && restaurants[a][0] > restaurants[b][0])
}

pub open spec fn find_by_id(
    restaurants: Seq<Vec<i32>>,
    id: i32,
    n: int,
) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else if restaurants[n - 1][0] == id {
        n - 1
    } else {
        find_by_id(restaurants, id, n - 1)
    }
}

impl Solution {
    pub fn filter_restaurants(
        restaurants: Vec<Vec<i32>>,
        vegan_friendly: i32,
        max_price: i32,
        max_distance: i32,
    ) -> (result: Vec<i32>)
        requires
            1 <= restaurants.len() <= 10000,
            forall |i: int| #![trigger restaurants[i]]
                0 <= i < restaurants.len() ==> {
                    &&& restaurants[i].len() == 5
                    &&& 1 <= restaurants[i][0] <= 100000
                    &&& 1 <= restaurants[i][1] <= 100000
                    &&& (restaurants[i][2] == 0 || restaurants[i][2] == 1)
                    &&& 1 <= restaurants[i][3] <= 100000
                    &&& 1 <= restaurants[i][4] <= 100000
                },
            vegan_friendly == 0 || vegan_friendly == 1,
            1 <= max_price <= 100000,
            1 <= max_distance <= 100000,
            forall |i: int, j: int|
                0 <= i < j < restaurants.len()
                ==> restaurants[i][0] != restaurants[j][0],
        ensures
            forall |j: int| 0 <= j < result.len() ==>
                0 <= find_by_id(restaurants@, #[trigger] result[j], restaurants@.len() as int)
                    < restaurants@.len(),
            forall |j: int| 0 <= j < result.len() ==>
                passes_filter(
                    restaurants@,
                    find_by_id(restaurants@, #[trigger] result[j], restaurants@.len() as int),
                    vegan_friendly,
                    max_price,
                    max_distance,
                ),
            forall |i: int| #![trigger restaurants[i]]
                0 <= i < restaurants.len()
                && passes_filter(restaurants@, i, vegan_friendly, max_price, max_distance)
                ==> exists |j: int|
                    0 <= j < result.len() && result[j] == restaurants[i][0],
            forall |j: int, k: int|
                0 <= j < k < result.len() ==> result[j] != result[k],
            forall |j: int, k: int|
                0 <= j < k < result.len() ==>
                ranked_higher(
                    restaurants@,
                    find_by_id(restaurants@, result[j], restaurants@.len() as int),
                    find_by_id(restaurants@, result[k], restaurants@.len() as int),
                ),
    {
    }
}

}
