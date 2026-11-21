import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Search one room. A state is a sorted box set and a connected player region.
// Every edge is one push; walking within a region is free.
function roomPushes(cells, outside, initial, targets, offsets) {
  cells = [...cells, outside];
  const n = cells.length;
  const index = new Map(cells.map((p, i) => [p, i]));
  const next = cells.map(p => offsets.map(d => index.get(p + d) ?? -1));
  const goals = targets.map(p => index.get(p));
  const boxes = initial.map(p => index.get(p)).sort((a, b) => a - b);
  const occupied = new Uint8Array(n);
  const seen = new Uint32Array(n);
  const queue = new Int16Array(n);
  let stamp = 0;
  function region(from) {
    const mark = ++stamp;
    let count = 1, minimum = from;
    queue[0] = from;
    seen[from] = mark;
    for (let head = 0; head < count; head++) {
      const p = queue[head];
      for (let d = 0; d < 4; d++) {
        const q = next[p][d];
        if (q >= 0 && !occupied[q] && seen[q] !== mark) {
          seen[q] = mark;
          queue[count++] = q;
          if (q < minimum) minimum = q;
        }
      }
    }
    return minimum;
  }

  // Reverse single-box push distances: both the old box square and the
  // player's supporting square must exist. Unreachable cells are dead squares.
  const distance = goals.map(goal => {
    const dist = new Int16Array(n).fill(1000);
    const work = [goal];
    dist[goal] = 0;
    for (let head = 0; head < work.length; head++) {
      const p = work[head];
      for (let d = 0; d < 4; d++) {
        const q = next[p][d];
        if (q >= 0 && q !== n - 1 && next[q][d] >= 0 && dist[q] === 1000) {
          dist[q] = dist[p] + 1;
          work.push(q);
        }
      }
    }
    return dist;
  });
  const live = cells.map((_, p) => p !== n - 1 && distance.some(dist => dist[p] < 1000));
  const encode = bs => bs.reduce((code, b) => code * 64 + b, 0);
  const estimates = new Map();
  function estimate(bs, code) {
    if (estimates.has(code)) return estimates.get(code);
    let best = 1000;
    function assign(i, used, sum) {
      if (sum >= best) return;
      if (i === bs.length) { best = sum; return; }
      for (let g = 0; g < goals.length; g++) {
        if (!(used & (1 << g))) assign(i + 1, used | (1 << g), sum + distance[g][bs[i]]);
      }
    }
    assign(0, 0, 0);
    estimates.set(code, best);
    return best;
  }

  // Minimum assignment cost is admissible: every solution assigns distinct
  // boxes to distinct goals, and other boxes can only obstruct these paths.
  const nodes = [], heap = [], bestState = new Map();
  function before(a, b) {
    const x = nodes[a], y = nodes[b];
    return x.f < y.f || (x.f === y.f && (x.g > y.g || (x.g === y.g && a < b)));
  }
  function insert(id) {
    let i = heap.length;
    heap.push(id);
    while (i > 0) {
      const parent = (i - 1) >> 1;
      if (!before(id, heap[parent])) break;
      heap[i] = heap[parent];
      i = parent;
    }
    heap[i] = id;
  }
  function pop() {
    const root = heap[0], last = heap.pop();
    if (heap.length) {
      let i = 0;
      while (i * 2 + 1 < heap.length) {
        let child = i * 2 + 1;
        if (child + 1 < heap.length && before(heap[child + 1], heap[child])) child++;
        if (!before(heap[child], last)) break;
        heap[i] = heap[child];
        i = child;
      }
      heap[i] = last;
    }
    return root;
  }
  function offer(bs, player, g, parent, from, direction) {
    const code = encode(bs), h = estimate(bs, code);
    if (h === 1000) return;
    const key = code * 64 + region(player);
    const old = bestState.get(key);
    if (old !== undefined && nodes[old].g <= g) return;
    const id = nodes.length;
    nodes.push({ boxes: bs, player, g, f: g + h, key, parent, from, direction });
    bestState.set(key, id);
    insert(id);
  }
  for (const b of boxes) occupied[b] = 1;
  offer(boxes, n - 1, 0, -1, -1, -1);
  while (heap.length) {
    const id = pop(), state = nodes[id];
    if (bestState.get(state.key) !== id) continue;
    if (state.f === state.g) {
      const pushes = [];
      for (let p = id; nodes[p].parent >= 0; p = nodes[p].parent) {
        pushes.push([cells[nodes[p].from], nodes[p].direction]);
      }
      return pushes.reverse();
    }
    occupied.fill(0);
    for (const b of state.boxes) occupied[b] = 1;
    region(state.player);
    // Successor floods reuse seen; preserve this state's reachability first.
    const reachable = seen.map(mark => +(mark === stamp));
    for (let i = 0; i < state.boxes.length; i++) {
      const b = state.boxes[i];
      for (let d = 0; d < 4; d++) {
        const to = next[b][d], behind = next[b][d ^ 1];
        if (to < 0 || behind < 0 || !live[to] || occupied[to] || !reachable[behind]) continue;
        const moved = state.boxes.slice();
        moved[i] = to;
        moved.sort((a, b) => a - b);
        occupied[b] = 0;
        occupied[to] = 1;
        offer(moved, b, state.g + 1, id, b, d);
        occupied[to] = 0;
        occupied[b] = 1;
      }
    }
  }
  throw new Error('Room has no solution');
}

function solve(text) {
  const rows = text.trimEnd().split('\n');
  const w = Math.max(...rows.map(row => row.length));
  const floor = new Uint8Array(w * rows.length), goal = new Uint8Array(floor.length);
  const boxes = new Set();
  let player = -1;
  rows.forEach((row, y) => [...row].forEach((ch, x) => {
    const p = y * w + x;
    if (ch !== '#') floor[p] = 1;
    if ('.*+'.includes(ch)) goal[p] = 1;
    if ('$*'.includes(ch)) boxes.add(p);
    if ('@+'.includes(ch)) player = p;
  }));
  const offsets = [-1, 1, -w, w], letters = 'lrud';
  const hallRow = Math.floor(player / w);
  const visited = new Uint8Array(floor.length);
  const rooms = [];
  for (let start = 0; start < floor.length; start++) {
    if (!floor[start] || visited[start] || Math.floor(start / w) === hallRow) continue;
    const cells = [start];
    let outside = -1;
    visited[start] = 1;
    for (let head = 0; head < cells.length; head++) {
      for (const d of offsets) {
        const q = cells[head] + d;
        if (!floor[q]) continue;
        if (Math.floor(q / w) === hallRow) { outside = q; continue; }
        if (!visited[q]) { visited[q] = 1; cells.push(q); }
      }
    }
    rooms.push({ cells, outside });
  }
  let answer = '';
  function walk(target) {
    const previous = new Int32Array(floor.length).fill(-1);
    const work = [player];
    previous[player] = player;
    for (let head = 0; head < work.length && previous[target] < 0; head++) {
      const p = work[head];
      for (const d of offsets) {
        const q = p + d;
        if (floor[q] && !boxes.has(q) && previous[q] < 0) {
          previous[q] = p;
          work.push(q);
        }
      }
    }
    if (previous[target] < 0) throw new Error('Unreachable push');
    const moves = [];
    for (let p = target; p !== player; p = previous[p]) moves.push(letters[offsets.indexOf(p - previous[p])]);
    answer += moves.reverse().join('');
    player = target;
  }
  for (const { cells, outside } of rooms) {
    const initial = cells.filter(p => boxes.has(p));
    if (!initial.length) continue;
    const pushes = roomPushes(cells, outside, initial, cells.filter(p => goal[p]), offsets);
    for (const [from, direction] of pushes) {
      const d = offsets[direction];
      walk(from - d);
      answer += letters[direction].toUpperCase();
      boxes.delete(from);
      boxes.add(from + d);
      player = from;
    }
  }
  return answer;
}

const input = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const output = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(input).sort()) {
  const moves = solve(readFileSync(join(input, id, 'level.txt'), 'utf8'));
  mkdirSync(join(output, id), { recursive: true });
  writeFileSync(join(output, id, 'solution.txt'), moves + '\n');
}
