use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_meeting_cells(ax: i64, ay: i64, bx: i64, by: i64, cx: i64, cy: i64) -> i64 {
        let mut ans: i64 = 1;

        let dx_b = bx - ax;
        let dx_c = cx - ax;
        if (dx_b > 0 && dx_c > 0) || (dx_b < 0 && dx_c < 0) {
            let ab = if dx_b >= 0 { dx_b } else { -dx_b };
            let ac = if dx_c >= 0 { dx_c } else { -dx_c };
            ans += if ab < ac { ab } else { ac };
        }

        let dy_b = by - ay;
        let dy_c = cy - ay;
        if (dy_b > 0 && dy_c > 0) || (dy_b < 0 && dy_c < 0) {
            let ab = if dy_b >= 0 { dy_b } else { -dy_b };
            let ac = if dy_c >= 0 { dy_c } else { -dy_c };
            ans += if ab < ac { ab } else { ac };
        }

        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let ax: i64 = it.next().unwrap().parse().unwrap();
        let ay: i64 = it.next().unwrap().parse().unwrap();
        let bx: i64 = it.next().unwrap().parse().unwrap();
        let by: i64 = it.next().unwrap().parse().unwrap();
        let cx: i64 = it.next().unwrap().parse().unwrap();
        let cy: i64 = it.next().unwrap().parse().unwrap();

        let ans = Solution::min_meeting_cells(ax, ay, bx, by, cx, cy);
        println!("{}", ans);
        i += 1;
    }
}
