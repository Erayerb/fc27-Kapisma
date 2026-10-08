const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const SIZE = 5;
const MAXOUT = 4;
const MINP = 5;
const FORMS = ['2-1-1', '1-2-1', '1-1-2', '2-0-2', '0-2-2', '3-0-1', '1-0-3'];
const FN = {
  '2-1-1': 'Dengeli',
  '1-2-1': 'Elmas',
  '1-1-2': 'Hücumcu',
  '2-0-2': 'Çift kanat',
  '0-2-2': 'Ofansif',
  '3-0-1': 'Beton savunma',
  '1-0-3': 'Tam hücum'
};
const IDX = { DEF: 0, MID: 1, FWD: 2 };
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

const DB = [
  ['Courtois', 'GK', 89], ['Alisson', 'GK', 88], ['Donnarumma', 'GK', 88], ['Maignan', 'GK', 87], ['Ter Stegen', 'GK', 86], ['Oblak', 'GK', 86],
  ['Van Dijk', 'DEF', 89], ['Dias', 'DEF', 87], ['Saliba', 'DEF', 87], ['Rüdiger', 'DEF', 86], ['Hakimi', 'DEF', 86], ['Alexander-Arnold', 'DEF', 86],
  ['Bastoni', 'DEF', 86], ['Gvardiol', 'DEF', 85], ['Theo Hernández', 'DEF', 85], ['Cancelo', 'DEF', 85], ['Marquinhos', 'DEF', 85], ['Ferdi Kadıoğlu', 'DEF', 80],
  ['Rodri', 'MID', 91], ['Bellingham', 'MID', 90], ['De Bruyne', 'MID', 89], ['Pedri', 'MID', 88], ['Valverde', 'MID', 88], ['Ødegaard', 'MID', 88],
  ['Vitinha', 'MID', 87], ['Barella', 'MID', 87], ['Kimmich', 'MID', 87], ['Çalhanoğlu', 'MID', 85], ['Arda Güler', 'MID', 82],
  ['Mbappé', 'FWD', 91], ['Haaland', 'FWD', 91], ['Vinícius Jr', 'FWD', 90], ['Kane', 'FWD', 90], ['Yamal', 'FWD', 89], ['Salah', 'FWD', 89],
  ['Dembélé', 'FWD', 88], ['Lautaro', 'FWD', 88], ['Osimhen', 'FWD', 87], ['Saka', 'FWD', 87], ['Lewandowski', 'FWD', 86], ['Kenan Yıldız', 'FWD', 80]
].map(([n, pos, o]) => ({ n, pos, o, base: o >= 89 ? 20 : o >= 87 ? 10 : 5 }));

const rooms = new Map();
const socketRoom = new Map();

function id() {
  return crypto.randomBytes(16).toString('hex');
}

function makeCode() {
  for (let n = 0; n < 40; n++) {
    let c = '';
    for (let i = 0; i < 4; i++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
  throw new Error('room code exhausted');
}

function shuffle(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function pick(a) {
  return a[crypto.randomInt(a.length)];
}

function left(g, t) {
  return SIZE - g.sq[t].length;
}

function need(g, t, pos) {
  return pos === 'GK' ? !g.sq[t].some(p => p.pos === 'GK') : g.sq[t].filter(p => p.pos !== 'GK').length < MAXOUT;
}

function reserveFor(g, t, p) {
  const r = left(g, t) - 1;
  const hasGK = g.sq[t].some(x => x.pos === 'GK') || p.pos === 'GK';
  if (r <= 0) return 0;
  if (hasGK) return r * MINP;
  const prices = g.queue.filter(x => x.pos === 'GK').map(x => x.base);
  return (prices.length ? Math.min(...prices) : 99) + (r - 1) * MINP;
}

function canBid(g, t, amt, p) {
  p = p || g.cur.p;
  return need(g, t, p.pos) && amt <= g.bud[t] - reserveFor(g, t, p);
}

function amts(g) {
  const c = g.cur;
  return c.bid ? [c.bid + 1, c.bid + 2, c.bid + 5, c.bid + 10] : [c.p.base, c.p.base + 2, c.p.base + 5, c.p.base + 10];
}

function perms(a) {
  if (a.length < 2) return [a];
  const r = [];
  a.forEach((x, i) => perms([...a.slice(0, i), ...a.slice(i + 1)]).forEach(p => r.push([x, ...p])));
  return r;
}

function lineup(g, t) {
  const [d, m, f] = g.form[t].split('-').map(Number);
  const slots = [...Array(d).fill('DEF'), ...Array(m).fill('MID'), ...Array(f).fill('FWD')];
  const out = g.sq[t].filter(p => p.pos !== 'GK');
  while (out.length < slots.length) out.push({ n: 'Boş slot', pos: 'MID', o: 40, paid: 0 });
  const gk = g.sq[t].find(p => p.pos === 'GK') || { n: 'Boş kaleci', pos: 'GK', o: 40, paid: 0 };
  const eff = (p, s) => p.o - 5 * Math.abs(IDX[p.pos] - IDX[s]);
  let best = null, bs = -1e9;
  perms(out).forEach(pm => {
    const sc = pm.reduce((s, p, i) => s + eff(p, slots[i]), 0);
    if (sc > bs) { bs = sc; best = pm; }
  });
  return [{ p: gk, slot: 'GK', eff: gk.o }, ...best.map((p, i) => ({ p, slot: slots[i], eff: eff(p, slots[i]) }))];
}

function av(a) {
  return a.length ? a.reduce((s, x) => s + x, 0) / a.length : null;
}

function wavg(pairs) {
  let s = 0, w = 0;
  pairs.forEach(([v, k]) => { if (v !== null) { s += v * k; w += k; } });
  return s / w;
}

function strength(L) {
  const g = s => av(L.filter(x => x.slot === s).map(x => x.eff));
  const D = g('DEF'), M = g('MID'), F = g('FWD'), G = g('GK');
  return { atk: wavg([[F, 3], [M, 2], [D, 0.5]]), def: wavg([[D, 3], [G, 2], [M, 1]]) };
}

function power(L) {
  const s = strength(L);
  return Math.round((s.atk + s.def) / 2);
}

function scorer(L) {
  const w = L.map(x => ({ p: x.p, w: ({ FWD: 5, MID: 3, DEF: 1, GK: 0 })[x.slot] * (x.eff / 80) }));
  let r = Math.random() * w.reduce((s, x) => s + x.w, 0);
  for (const x of w) { r -= x.w; if (r <= 0) return x.p; }
  return w[1].p;
}

function simulate(g) {
  const st = [strength(g.L[0]), strength(g.L[1])];
  const T = [];
  const goals = [0, 0];
  const add = (m, txt, o) => T.push({ m, txt, g: [...goals], ...(o || {}) });
  add("0'", `🔔 Hakem düdüğü çaldı! ${g.names[0]} (${g.form[0]}) - ${g.names[1]} (${g.form[1]})`, { sys: 1 });
  for (let m = 4; m <= 88; m += 4) {
    const pa = st[0].atk / (st[0].atk + st[1].atk);
    const t = Math.random() < pa ? 0 : 1;
    const o = 1 - t;
    const p = scorer(g.L[t]);
    const n = g.names[t];
    add(m + "'", pick([
      `${n} orta sahada topu çeviriyor.`,
      `${p.n} topu ileri taşıyor.`,
      'Kanattan bir orta geliyor...',
      `${n} baskıyı artırdı.`,
      `${p.n} savunmayı geçmeye çalışıyor.`
    ]), { mute: 1 });
    const pg = Math.min(0.35, Math.max(0.03, 0.14 + (st[t].atk - st[o].def) * 0.008));
    if (Math.random() < pg) {
      goals[t]++;
      add(m + "'", `⚽ GOL! ${p.n} (${n}) ağlara gönderdi!`, { goal: 1 });
    } else {
      const dd = pick(g.L[o].slice(1)).p.n;
      add(m + "'", pick([
        `${p.n} şut çekti, ${g.L[o][0].p.n} son anda çıkardı!`,
        `${p.n} vuruşu auta gitti.`,
        `${p.n}'in şutu direkten döndü!`,
        `${dd} son anda araya girdi, tehlike geçti.`,
        `Korner kazandı ${n}, ama atak sonuçsuz kaldı.`,
        `🟨 ${dd} sert müdahale yaptı, sarı kart gördü.`
      ]));
    }
    if (m === 44) add("45'", '⏸ Devre arası. Takımlar soyunma odasına gidiyor.', { sys: 1 });
  }
  add("90'", '🏁 Hakem final düdüğünü çaldı.', { sys: 1 });
  let pen = null;
  if (goals[0] === goals[1]) {
    add("90'", '🥅 Beraberlik! Seri penaltı atışlarına geçiliyor.', { sys: 1 });
    const sc = [0, 0];
    let i = 0, done = false;
    while (!done) {
      for (const t of [0, 1]) {
        const ks = g.L[t].slice(1);
        const p = ks[i % ks.length];
        const ok = Math.random() < 0.76;
        if (ok) sc[t]++;
        add('PEN', `${p.n} (${g.names[t]}) penaltıyı ${ok ? 'gole çevirdi ✅' : 'kaçırdı ❌'} · ${sc[0]}-${sc[1]}`, { pen: [...sc] });
      }
      i++;
      if (i >= 5 && sc[0] !== sc[1]) done = true;
      if (i >= 15) { if (sc[0] === sc[1]) sc[0]++; done = true; }
    }
    pen = sc;
  }
  return { T, g: [...goals], pen };
}

function nextPlayer(g) {
  if (left(g, 0) === 0 && left(g, 1) === 0) return finishAuction(g);
  for (const o of [g.nom, 1 - g.nom]) {
    const i = g.queue.findIndex(p => need(g, o, p.pos) && canBid(g, o, p.base, p));
    if (i >= 0) {
      const p = g.queue.splice(i, 1)[0];
      g.cur = { p, bid: 0, leader: null, turn: o, opener: o };
      g.nom = 1 - o;
      return;
    }
  }
  finishAuction(g);
}

function finishAuction(g) {
  if (left(g, 0) > 0 || left(g, 1) > 0) {
    g.sq = [[], []];
    g.bud = [g.B, g.B];
    g.queue = shuffle(DB.map(x => ({ ...x })));
    g.msg = '⚠ Boş slot kaldı, açık artırma sırayla baştan yapılıyor.';
    nextPlayer(g);
    return;
  }
  g.cur = null;
  g.phase = 'formation';
  g.ready = [false, false];
}

function startAuction(room) {
  const b = room.budget;
  room.game = {
    phase: 'auction',
    B: b,
    names: [room.players[0].name, room.players[1].name],
    bud: [b, b],
    sq: [[], []],
    queue: shuffle(DB.map(x => ({ ...x }))),
    nom: crypto.randomInt(2),
    cur: null,
    msg: '',
    form: ['2-1-1', '2-1-1'],
    ready: [false, false],
    L: null,
    match: null
  };
  nextPlayer(room.game);
}

function newRoom() {
  const code = makeCode();
  const room = {
    code,
    budget: 100,
    players: [null, null],
    game: { phase: 'lobby' }
  };
  rooms.set(code, room);
  return room;
}

function occupied(room) {
  return room.players.filter(Boolean).length;
}

function viewFor(room, seat) {
  const g = room.game;
  const players = room.players.map((p, i) => p ? {
    seat: i,
    name: p.name,
    connected: !!p.socketId,
    host: i === 0
  } : null);
  const base = {
    code: room.code,
    seat,
    host: seat === 0,
    budget: room.budget,
    players,
    occupied: occupied(room),
    phase: g.phase,
    forms: FORMS,
    formNames: FN
  };
  if (g.phase === 'lobby') return base;

  const pub = {
    ...base,
    names: g.names,
    bud: g.bud,
    sq: g.sq,
    form: g.form,
    msg: g.msg,
    queueLen: g.queue ? g.queue.length : 0,
    cur: g.cur,
    ready: g.ready
  };

  if (g.phase === 'auction' && g.cur) {
    const t = g.cur.turn;
    pub.myTurn = seat === t;
    pub.forced = g.cur.leader === null;
    pub.maxBid = Math.max(0, g.bud[t] - reserveFor(g, t, g.cur.p));
    pub.amounts = amts(g).map(a => ({ a, ok: canBid(g, t, a) }));
    pub.canPass = g.cur.leader !== null;
  }

  if (g.phase === 'formation' || g.phase === 'match' || g.phase === 'end') {
    const L0 = g.L && g.phase !== 'formation' ? g.L[0] : lineup(g, 0);
    const L1 = g.L && g.phase !== 'formation' ? g.L[1] : lineup(g, 1);
    pub.lineups = [L0, L1];
    pub.power = [power(L0), power(L1)];
  }

  if (g.match) {
    pub.match = {
      T: g.match.T,
      g: g.match.g,
      pen: g.match.pen,
      skip: !!g.match.skip
    };
  }
  return pub;
}

function emitRoom(io, room) {
  for (const p of room.players) {
    if (!p || !p.socketId) continue;
    io.to(p.socketId).emit('state', viewFor(room, p.seat));
  }
}

function findByToken(token) {
  for (const room of rooms.values()) {
    const p = room.players.find(x => x && x.token === token);
    if (p) return { room, player: p };
  }
  return null;
}

function leaveSocket(io, socket) {
  const code = socketRoom.get(socket.id);
  if (!code) return;
  socketRoom.delete(socket.id);
  const room = rooms.get(code);
  if (!room) return;
  const p = room.players.find(x => x && x.socketId === socket.id);
  if (p) p.socketId = null;
  socket.leave(code);
  if (room.game.phase === 'lobby' && occupied(room) === 0) {
    rooms.delete(code);
    return;
  }
  emitRoom(io, room);
}

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

io.on('connection', socket => {
  socket.on('createRoom', (data = {}) => {
    try {
      leaveSocket(io, socket);
      const room = newRoom();
      const name = String(data.name || '').trim().slice(0, 20) || 'Kırmızı Şimşekler';
      const player = { token: id(), seat: 0, name, socketId: socket.id };
      room.players[0] = player;
      socket.join(room.code);
      socketRoom.set(socket.id, room.code);
      socket.emit('joined', { code: room.code, token: player.token, seat: 0 });
      emitRoom(io, room);
    } catch (err) {
      socket.emit('err', { message: 'Oda oluşturulamadı.' });
    }
  });

  socket.on('joinRoom', (data = {}) => {
    const code = String(data.code || '').replace(/\s+/g, '').trim().toUpperCase();
    const room = rooms.get(code);
    if (!room) return socket.emit('err', { message: 'Oda bulunamadı.' });
    if (room.players[1]) return socket.emit('err', { message: 'Oda dolu.' });
    leaveSocket(io, socket);
    const name = String(data.name || '').trim().slice(0, 20) || 'Mavi Fırtına';
    const player = { token: id(), seat: 1, name, socketId: socket.id };
    room.players[1] = player;
    socket.join(room.code);
    socketRoom.set(socket.id, room.code);
    socket.emit('joined', { code: room.code, token: player.token, seat: 1 });
    emitRoom(io, room);
  });

  socket.on('rejoin', (data = {}) => {
    const found = findByToken(String(data.token || ''));
    if (!found) return socket.emit('err', { message: 'Oturum bulunamadı. Yeni oda oluştur veya katıl.' });
    const { room, player } = found;
    if (player.socketId && player.socketId !== socket.id) {
      const old = player.socketId;
      io.to(old).emit('kicked', { message: 'Başka bir sekmeden bağlandın.' });
      socketRoom.delete(old);
    }
    leaveSocket(io, socket);
    player.socketId = socket.id;
    socket.join(room.code);
    socketRoom.set(socket.id, room.code);
    socket.emit('joined', { code: room.code, token: player.token, seat: player.seat });
    emitRoom(io, room);
  });

  socket.on('setName', (data = {}) => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'lobby') return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p) return;
    p.name = String(data.name || '').trim().slice(0, 20) || (p.seat === 0 ? 'Kırmızı Şimşekler' : 'Mavi Fırtına');
    emitRoom(io, room);
  });

  socket.on('setBudget', (data = {}) => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'lobby') return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p || p.seat !== 0) return;
    const b = Math.max(30, Math.min(1000, Math.round(Number(data.budget) || 100)));
    room.budget = b;
    emitRoom(io, room);
  });

  socket.on('startGame', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'lobby') return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p || p.seat !== 0) return;
    if (!room.players[0] || !room.players[1]) {
      return socket.emit('err', { message: 'Oyunu başlatmak için 2 oyuncu gerekli.' });
    }
    startAuction(room);
    emitRoom(io, room);
  });

  socket.on('bid', (data = {}) => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'auction' || !room.game.cur) return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    const g = room.game;
    const c = g.cur;
    if (!p || p.seat !== c.turn) return;
    const amt = Number(data.amt);
    if (!amts(g).includes(amt) || !canBid(g, c.turn, amt)) return;
    c.bid = amt;
    c.leader = c.turn;
    c.turn = 1 - c.turn;
    g.msg = `${g.names[p.seat]} ${amt}M teklif verdi`;
    if (!canBid(g, c.turn, amts(g)[0])) {
      g.msg += ` · ${g.names[c.turn]} artıramıyor`;
      g.bud[c.leader] -= c.bid;
      g.sq[c.leader].push({ ...c.p, paid: c.bid });
      g.msg = `✅ ${c.p.n} → ${g.names[c.leader]} (${c.bid}M)`;
      nextPlayer(g);
    }
    emitRoom(io, room);
  });

  socket.on('pass', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'auction' || !room.game.cur) return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    const g = room.game;
    const c = g.cur;
    if (!p || p.seat !== c.turn || c.leader === null) return;
    g.bud[c.leader] -= c.bid;
    g.sq[c.leader].push({ ...c.p, paid: c.bid });
    g.msg = `✅ ${c.p.n} → ${g.names[c.leader]} (${c.bid}M)`;
    nextPlayer(g);
    emitRoom(io, room);
  });

  socket.on('setForm', (data = {}) => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'formation') return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p) return;
    const v = String(data.form || '');
    if (!FORMS.includes(v)) return;
    room.game.form[p.seat] = v;
    room.game.ready[p.seat] = false;
    emitRoom(io, room);
  });

  socket.on('readyMatch', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'formation') return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p) return;
    room.game.ready[p.seat] = true;
    if (room.game.ready[0] && room.game.ready[1]) {
      const g = room.game;
      g.L = [lineup(g, 0), lineup(g, 1)];
      g.match = { ...simulate(g), skip: false };
      g.phase = 'match';
    }
    emitRoom(io, room);
  });

  socket.on('skipMatch', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'match' || !room.game.match) return;
    room.game.match.skip = true;
    room.game.phase = 'end';
    emitRoom(io, room);
  });

  socket.on('matchDone', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'match') return;
    room.game.phase = 'end';
    emitRoom(io, room);
  });

  socket.on('rematch', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || (room.game.phase !== 'end' && room.game.phase !== 'match')) return;
    const g = room.game;
    g.L = [lineup(g, 0), lineup(g, 1)];
    g.match = { ...simulate(g), skip: false };
    g.phase = 'match';
    emitRoom(io, room);
  });

  socket.on('backToFormation', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room || room.game.phase !== 'end') return;
    room.game.phase = 'formation';
    room.game.ready = [false, false];
    room.game.match = null;
    room.game.L = null;
    emitRoom(io, room);
  });

  socket.on('newGame', () => {
    const code = socketRoom.get(socket.id);
    const room = rooms.get(code);
    if (!room) return;
    const p = room.players.find(x => x && x.socketId === socket.id);
    if (!p || p.seat !== 0) return;
    room.game = { phase: 'lobby' };
    emitRoom(io, room);
  });

  socket.on('disconnect', () => leaveSocket(io, socket));
});

server.listen(PORT, () => {
  console.log(`FC27 Kapışma http://localhost:${PORT}`);
});
