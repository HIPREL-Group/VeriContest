use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
	pub open spec fn row_move_cost(row_costs: Seq<i32>, cur: int, target: int) -> int
		recommends
			0 <= cur < row_costs.len(),
			0 <= target < row_costs.len(),
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
		decreases if cur <= target { target - cur } else { cur - target },
	{
		if cur == target {
			0
		} else if cur < target {
			row_costs[cur + 1] as int + Self::row_move_cost(row_costs, cur + 1, target)
		} else {
			row_costs[cur - 1] as int + Self::row_move_cost(row_costs, cur - 1, target)
		}
	}

	pub open spec fn col_move_cost(col_costs: Seq<i32>, cur: int, target: int) -> int
		recommends
			0 <= cur < col_costs.len(),
			0 <= target < col_costs.len(),
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
		decreases if cur <= target { target - cur } else { cur - target },
	{
		if cur == target {
			0
		} else if cur < target {
			col_costs[cur + 1] as int + Self::col_move_cost(col_costs, cur + 1, target)
		} else {
			col_costs[cur - 1] as int + Self::col_move_cost(col_costs, cur - 1, target)
		}
	}

	proof fn lemma_row_step_up(row_costs: Seq<i32>, cur: int, target: int)
		requires
			0 <= cur < target < row_costs.len(),
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
		ensures
			Self::row_move_cost(row_costs, cur, target)
				== row_costs[cur + 1] as int + Self::row_move_cost(row_costs, cur + 1, target),
	{
	}

	proof fn lemma_row_step_down(row_costs: Seq<i32>, cur: int, target: int)
		requires
			0 <= target < cur < row_costs.len(),
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
		ensures
			Self::row_move_cost(row_costs, cur, target)
				== row_costs[cur - 1] as int + Self::row_move_cost(row_costs, cur - 1, target),
	{
	}

	proof fn lemma_col_step_up(col_costs: Seq<i32>, cur: int, target: int)
		requires
			0 <= cur < target < col_costs.len(),
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
		ensures
			Self::col_move_cost(col_costs, cur, target)
				== col_costs[cur + 1] as int + Self::col_move_cost(col_costs, cur + 1, target),
	{
	}

	proof fn lemma_col_step_down(col_costs: Seq<i32>, cur: int, target: int)
		requires
			0 <= target < cur < col_costs.len(),
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
		ensures
			Self::col_move_cost(col_costs, cur, target)
				== col_costs[cur - 1] as int + Self::col_move_cost(col_costs, cur - 1, target),
	{
	}

	pub fn min_cost(start_pos: Vec<i32>, home_pos: Vec<i32>, row_costs: Vec<i32>, col_costs: Vec<i32>) -> (result: i32)
		requires
			start_pos.len() == 2,
			home_pos.len() == 2,
			1 <= row_costs.len() <= 100_000,
			1 <= col_costs.len() <= 100_000,
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
			0 <= start_pos[0] < row_costs.len(),
			0 <= home_pos[0] < row_costs.len(),
			0 <= start_pos[1] < col_costs.len(),
			0 <= home_pos[1] < col_costs.len(),
		ensures
			result as int
				== Self::row_move_cost(row_costs@, start_pos[0] as int, home_pos[0] as int)
					+ Self::col_move_cost(col_costs@, start_pos[1] as int, home_pos[1] as int),
	{
		let mut r = start_pos[0];
		let mut c = start_pos[1];
		let sr = start_pos[0];
		let sc = start_pos[1];
		let hr = home_pos[0];
		let hc = home_pos[1];
		let mut result_i64: i64 = 0;

		if r < hr {
			while r < hr
				invariant
					1 <= row_costs.len() <= 100_000,
					forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
					0 <= sr < row_costs.len(),
					0 <= hr < row_costs.len(),
					sr <= r <= hr,
					result_i64 as int + Self::row_move_cost(row_costs@, r as int, hr as int)
						== Self::row_move_cost(row_costs@, sr as int, hr as int),
					0 <= result_i64 as int <= 10_000 * (r as int - sr as int),
				decreases hr - r,
			{
				let ghost old_r: int = r as int;
				let ghost old_result: int = result_i64 as int;
				proof {
					Self::lemma_row_step_up(row_costs@, old_r, hr as int);
				}
				r = r + 1;
				result_i64 = result_i64 + row_costs[r as usize] as i64;
				proof {
					assert(result_i64 as int == old_result + row_costs[old_r + 1] as int);
					assert(result_i64 as int + Self::row_move_cost(row_costs@, r as int, hr as int)
						== Self::row_move_cost(row_costs@, sr as int, hr as int));
					assert(0 <= result_i64 as int <= 10_000 * (r as int - sr as int)) by (nonlinear_arith)
						requires
							0 <= old_result <= 10_000 * (old_r - sr as int),
							result_i64 as int == old_result + row_costs[old_r + 1] as int,
							0 <= row_costs[old_r + 1] <= 10_000,
							r as int == old_r + 1,
					{
					}
				}
			}
		} else {
			while r > hr
				invariant
					1 <= row_costs.len() <= 100_000,
					forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
					0 <= sr < row_costs.len(),
					0 <= hr < row_costs.len(),
					hr <= r <= sr,
					result_i64 as int + Self::row_move_cost(row_costs@, r as int, hr as int)
						== Self::row_move_cost(row_costs@, sr as int, hr as int),
					0 <= result_i64 as int <= 10_000 * (sr as int - r as int),
				decreases r - hr,
			{
				let ghost old_r: int = r as int;
				let ghost old_result: int = result_i64 as int;
				proof {
					Self::lemma_row_step_down(row_costs@, old_r, hr as int);
				}
				r = r - 1;
				result_i64 = result_i64 + row_costs[r as usize] as i64;
				proof {
					assert(result_i64 as int == old_result + row_costs[old_r - 1] as int);
					assert(result_i64 as int + Self::row_move_cost(row_costs@, r as int, hr as int)
						== Self::row_move_cost(row_costs@, sr as int, hr as int));
					assert(0 <= result_i64 as int <= 10_000 * (sr as int - r as int)) by (nonlinear_arith)
						requires
							0 <= old_result <= 10_000 * (sr as int - old_r),
							result_i64 as int == old_result + row_costs[old_r - 1] as int,
							0 <= row_costs[old_r - 1] <= 10_000,
							r as int == old_r - 1,
					{
					}
				}
			}
		}

		proof {
			assert(r == hr);
			assert(result_i64 as int == Self::row_move_cost(row_costs@, sr as int, hr as int));
			assert(result_i64 as int <= 1_000_000_000);
		}

		if c < hc {
			while c < hc
				invariant
					1 <= row_costs.len() <= 100_000,
					1 <= col_costs.len() <= 100_000,
					forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
					forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
					0 <= sr < row_costs.len(),
					0 <= hr < row_costs.len(),
					0 <= sc < col_costs.len(),
					0 <= hc < col_costs.len(),
					sc <= c <= hc,
					result_i64 as int
						== Self::row_move_cost(row_costs@, sr as int, hr as int)
							+ Self::col_move_cost(col_costs@, sc as int, hc as int)
							- Self::col_move_cost(col_costs@, c as int, hc as int),
					0 <= result_i64 as int <= 1_000_000_000 + 10_000 * (c as int - sc as int),
				decreases hc - c,
			{
				let ghost old_c: int = c as int;
				let ghost old_result: int = result_i64 as int;
				proof {
					Self::lemma_col_step_up(col_costs@, old_c, hc as int);
				}
				c = c + 1;
				result_i64 = result_i64 + col_costs[c as usize] as i64;
				proof {
					assert(result_i64 as int == old_result + col_costs[old_c + 1] as int);
					assert(result_i64 as int
						== Self::row_move_cost(row_costs@, sr as int, hr as int)
							+ Self::col_move_cost(col_costs@, sc as int, hc as int)
							- Self::col_move_cost(col_costs@, c as int, hc as int));
					assert(0 <= result_i64 as int <= 1_000_000_000 + 10_000 * (c as int - sc as int)) by (nonlinear_arith)
						requires
							0 <= old_result <= 1_000_000_000 + 10_000 * (old_c - sc as int),
							result_i64 as int == old_result + col_costs[old_c + 1] as int,
							0 <= col_costs[old_c + 1] <= 10_000,
							c as int == old_c + 1,
					{
					}
				}
			}
		} else {
			while c > hc
				invariant
					1 <= row_costs.len() <= 100_000,
					1 <= col_costs.len() <= 100_000,
					forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
					forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
					0 <= sr < row_costs.len(),
					0 <= hr < row_costs.len(),
					0 <= sc < col_costs.len(),
					0 <= hc < col_costs.len(),
					hc <= c <= sc,
					result_i64 as int
						== Self::row_move_cost(row_costs@, sr as int, hr as int)
							+ Self::col_move_cost(col_costs@, sc as int, hc as int)
							- Self::col_move_cost(col_costs@, c as int, hc as int),
					0 <= result_i64 as int <= 1_000_000_000 + 10_000 * (sc as int - c as int),
				decreases c - hc,
			{
				let ghost old_c: int = c as int;
				let ghost old_result: int = result_i64 as int;
				proof {
					Self::lemma_col_step_down(col_costs@, old_c, hc as int);
				}
				c = c - 1;
				result_i64 = result_i64 + col_costs[c as usize] as i64;
				proof {
					assert(result_i64 as int == old_result + col_costs[old_c - 1] as int);
					assert(result_i64 as int
						== Self::row_move_cost(row_costs@, sr as int, hr as int)
							+ Self::col_move_cost(col_costs@, sc as int, hc as int)
							- Self::col_move_cost(col_costs@, c as int, hc as int));
					assert(0 <= result_i64 as int <= 1_000_000_000 + 10_000 * (sc as int - c as int)) by (nonlinear_arith)
						requires
							0 <= old_result <= 1_000_000_000 + 10_000 * (sc as int - old_c),
							result_i64 as int == old_result + col_costs[old_c - 1] as int,
							0 <= col_costs[old_c - 1] <= 10_000,
							c as int == old_c - 1,
					{
					}
				}
			}
		}

		proof {
			assert(c == hc);
			assert(result_i64 as int
				== Self::row_move_cost(row_costs@, sr as int, hr as int)
					+ Self::col_move_cost(col_costs@, sc as int, hc as int));
			assert(result_i64 as int <= 2_000_000_000);
			assert(result_i64 <= i32::MAX as i64);
		}

		result_i64 as i32
	}
}

}
