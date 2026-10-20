const test = require('node:test');
const assert = require('node:assert/strict');
const { selectLeaderboardEntries: select, sortLeaderboardRows: sortRows, leaderboardSafeUrl: safeUrl } = require('../docs/static/leaderboard.js');
const filters = {track:'agent',task:'End2End',inputMode:'nl',split:'full',protocol:'agreed',query:''};
const entry = (id, score, overrides = {}) => ({id,system:id,team:'Team',models:['model'],track:'agent',task:'End2End',input_mode:'nl',split:'full',protocol_id:'agreed',status:'evaluation_checked',rankable:true,score,...overrides});

test('pending submissions cannot outrank checked submissions', () => {
  const rows = select([entry('pending',100,{status:'submitted',rankable:false,score:null,protocol_id:null}),entry('checked',10)],filters);
  assert.equal(rows[0].id,'checked'); assert.equal(rows[0].rank,1); assert.equal(rows[1].rank,null);
});
test('search preserves the rank within the comparison group', () => {
  const rows = select([entry('a',20),entry('b',10)],{...filters,query:'b'});
  assert.equal(rows[0].rank,2);
});
test('ties share competition rank; missing scores are not zero scores', () => {
  const rows = select([entry('a',20),entry('b',20),entry('c',0),entry('d',null,{rankable:false,status:'submitted'})],filters);
  assert.deepEqual(rows.map(r=>r.rank),[1,1,3,null]);
});
test('different settings never form a combined ranking', () => {
  const input = [entry('a',20),entry('b',90,{protocol_id:'different'})];
  assert.deepEqual(select(input,filters).map(r=>r.id),['a']);
  assert.ok(select(input,{...filters,protocol:''}).every(r=>r.rank===null));
});
test('tracks, task inputs and splits stay separate', () => {
  const input = [entry('a',20),entry('b',90,{track:'fixed_prompt'}),entry('c',90,{split:'leetcode'}),entry('d',90,{task:'CodeGen'}),entry('e',90,{input_mode:'spec'})];
  assert.deepEqual(select(input,filters).map(r=>r.id),['a']);
});
test('full-split entries appear in each split view with that split\'s score', () => {
  const full = entry('full',50,{split_scores:{full:50,leetcode:60,codeforces:25},split_problem_counts:{full:4,leetcode:3,codeforces:1}});
  const lc = entry('lc',55,{split:'leetcode',split_scores:{leetcode:55},split_problem_counts:{leetcode:3}});
  const rows = select([full,lc],{...filters,split:'leetcode'});
  assert.deepEqual(rows.map(r=>[r.id,r.score,r.rank,r.problem_count]),[['full',60,1,3],['lc',55,2,3]]);
  assert.deepEqual(select([full,lc],{...filters,split:'codeforces'}).map(r=>[r.id,r.score]),[['full',25]]);
  assert.deepEqual(select([full,lc],filters).map(r=>r.id),['full']);
});
test('Lite view ranks full-split entries on Lite next to Lite entries', () => {
  const full = entry('full',50,{split_scores:{full:50,leetcode:60,codeforces:25,lite:40},split_problem_counts:{full:4,leetcode:3,codeforces:1,lite:2}});
  const lite = entry('lite',45,{split:'lite',split_scores:{lite:45},split_problem_counts:{lite:2}});
  assert.deepEqual(select([full,lite],{...filters,split:'lite'}).map(r=>[r.id,r.score,r.rank]),[['lite',45,1],['full',40,2]]);
  assert.deepEqual(select([full,lite],filters).map(r=>r.id),['full']);
});
test('Lite view links Lite trajectories when an entry has them', () => {
  const counts = {split_scores:{full:50,lite:40},split_problem_counts:{full:4,lite:2}};
  const withLite = entry('a',50,{...counts,trajectory_url:'https://example.org/full',split_trajectory_urls:{lite:'https://example.org/lite'}});
  const fullOnly = entry('b',50,{...counts,trajectory_url:'https://example.org/b-full'});
  assert.deepEqual(select([withLite,fullOnly],{...filters,split:'lite'}).map(r=>r.trajectory_url),['https://example.org/lite','https://example.org/b-full']);
  assert.deepEqual(select([withLite],filters).map(r=>r.trajectory_url),['https://example.org/full']);
});
test('column sorting keeps ranks, puts missing values last, and keeps rank order for ties', () => {
  const rows = select([entry('a',20,{date:'2026-10-02',org:'Zeta'}),entry('b',30,{date:'2026-10-01',org:'Alpha'}),
    entry('c',20,{date:'2026-10-03',org:'Alpha'}),entry('d',null,{rankable:false,status:'submitted',date:'2026-10-04',org:'Mid'})],filters);
  assert.deepEqual(rows.map(r=>r.id),['b','a','c','d']);
  assert.deepEqual(sortRows(rows,{key:'score',dir:'asc'}).map(r=>r.id),['a','c','b','d']);
  assert.deepEqual(sortRows(rows,{key:'score',dir:'desc'}).map(r=>r.id),['b','a','c','d']);
  assert.deepEqual(sortRows(rows,{key:'rank',dir:'desc'}).map(r=>[r.id,r.rank]),[['a',2],['c',2],['b',1],['d',null]]);
  assert.deepEqual(sortRows(rows,{key:'date',dir:'desc'}).map(r=>r.id),['d','c','a','b']);
  assert.deepEqual(sortRows(rows,{key:'org',dir:'asc'}).map(r=>r.id),['b','c','d','a']);
  assert.deepEqual(rows.map(r=>r.id),['b','a','c','d']);
});
test('reject unsafe links and embedded credentials', () => {
  for (const value of ['javascript:alert(1)','data:text/html,test','http://example.org','https://user:password@example.org',null]) assert.equal(safeUrl(value),null);
  assert.equal(safeUrl('https://example.org/artifacts'),'https://example.org/artifacts');
});
