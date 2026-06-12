/* 十三张 联机服务器
 * Node.js + ws。房间制:建房得房号,朋友凭房号入座,开局时空位由AI补足。
 * 金币为虚拟币,无真实支付。
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const WebSocket = require('ws');

const PORT = process.env.PORT || 3000;
const ADMIN_KEY = process.env.ADMIN_KEY || 'admin123';
const COIN_PER_ROAD = 10, COIN_PER_YUAN = 300, ARRANGE_MS = 30000;
const START_BALANCE = 3000;

/* ================= 牌型逻辑 ================= */
function makeDeck(){let d=[];for(let s=0;s<4;s++)for(let r=2;r<=14;r++)d.push({r,s});return d;}
function shuffle(a){for(let i=a.length-1;i>0;i--){let j=Math.random()*(i+1)|0;[a[i],a[j]]=[a[j],a[i]];}return a;}
function evaluate5(cs){
  const rs=cs.map(c=>c.r).sort((a,b)=>b-a);
  const counts={};rs.forEach(r=>counts[r]=(counts[r]||0)+1);
  const groups=Object.entries(counts).map(([r,c])=>[c,+r]).sort((a,b)=>b[0]-a[0]||b[1]-a[1]);
  const isFlush=cs.every(c=>c.s===cs[0].s);
  const uniq=[...new Set(rs)];
  let isStraight=false,sHigh=0;
  if(uniq.length===5){
    if(uniq[0]-uniq[4]===4){isStraight=true;sHigh=uniq[0];}
    else if(uniq[0]===14&&uniq[1]===5&&uniq[4]===2){isStraight=true;sHigh=5;}
  }
  let cat,tb;
  if(isStraight&&isFlush){cat=8;tb=[sHigh];}
  else if(groups[0][0]===4){cat=7;tb=[groups[0][1],groups[1][1]];}
  else if(groups[0][0]===3&&groups[1][0]>=2){cat=6;tb=[groups[0][1],groups[1][1]];}
  else if(isFlush){cat=5;tb=rs.slice();}
  else if(isStraight){cat=4;tb=[sHigh];}
  else if(groups[0][0]===3){cat=3;tb=[groups[0][1],...rs.filter(r=>r!==groups[0][1])];}
  else if(groups[0][0]===2&&groups[1][0]===2){const p=[groups[0][1],groups[1][1]].sort((a,b)=>b-a);
    cat=2;tb=[...p,rs.find(r=>r!==p[0]&&r!==p[1])];}
  else if(groups[0][0]===2){cat=1;tb=[groups[0][1],...rs.filter(r=>r!==groups[0][1])];}
  else{cat=0;tb=rs.slice();}
  return {cat,compCat:cat,tb};
}
function evaluate3(cs){
  const rs=cs.map(c=>c.r).sort((a,b)=>b-a);
  const counts={};rs.forEach(r=>counts[r]=(counts[r]||0)+1);
  const groups=Object.entries(counts).map(([r,c])=>[c,+r]).sort((a,b)=>b[0]-a[0]||b[1]-a[1]);
  let cat,tb;
  if(groups[0][0]===3){cat=2;tb=[groups[0][1]];}
  else if(groups[0][0]===2){cat=1;tb=[groups[0][1],...rs.filter(r=>r!==groups[0][1])];}
  else{cat=0;tb=rs.slice();}
  return {cat,compCat:cat===2?3:cat,tb};
}
function cmpKey(a,b){
  if(a.compCat!==b.compCat)return a.compCat-b.compCat;
  const n=Math.max(a.tb.length,b.tb.length);
  for(let i=0;i<n;i++){const x=a.tb[i]||0,y=b.tb[i]||0;if(x!==y)return x-y;}
  return 0;
}
function strengthVal(e){let v=e.compCat*1e10;for(let i=0;i<5;i++)v+=(e.tb[i]||0)*Math.pow(15,4-i);return v;}
function combinations(arr,k){
  const res=[],n=arr.length,idx=[];
  (function rec(start,depth){
    if(depth===k){res.push(idx.map(i=>arr[i]));return;}
    for(let i=start;i<n;i++){idx[depth]=i;rec(i+1,depth+1);}
  })(0,0);
  return res;
}
function bestArrange(cards){
  let best=null,bestVal=-Infinity;
  for(const back of combinations(cards,5)){
    const be=evaluate5(back);
    const rem=cards.filter(c=>!back.includes(c));
    for(const mid of combinations(rem,5)){
      const me=evaluate5(mid);
      if(cmpKey(be,me)<0)continue;
      const front=rem.filter(c=>!mid.includes(c));
      const fe=evaluate3(front);
      if(cmpKey(me,fe)<0)continue;
      const val=strengthVal(be)*100+strengthVal(me)*10+strengthVal(fe);
      if(val>bestVal){bestVal=val;best={front,mid,back};}
    }
  }
  return best;
}
function roadPoints(roadIdx,ev){
  if(roadIdx===0)return ev.cat===2?3:1;
  if(roadIdx===1){if(ev.cat===8)return 10;if(ev.cat===7)return 8;if(ev.cat===6)return 2;return 1;}
  if(ev.cat===8)return 5;if(ev.cat===7)return 4;return 1;
}
function scoreMatch(P,Q){
  const detail=[];let pts=0,pWins=0,qWins=0;
  for(let i=0;i<3;i++){
    let c;
    if(P.foul&&Q.foul)c=0;
    else if(P.foul)c=-1;
    else if(Q.foul)c=1;
    else c=cmpKey(P.evals[i],Q.evals[i]);
    if(c>0){const b=roadPoints(i,P.evals[i]);pts+=b;pWins++;detail.push({i,res:1,b});}
    else if(c<0){const b=roadPoints(i,Q.evals[i]);pts-=b;qWins++;detail.push({i,res:-1,b});}
    else detail.push({i,res:0,b:0});
  }
  let shoot=0;
  if(!P.foul&&!Q.foul){
    if(pWins===3&&qWins===0){pts*=2;shoot=1;}
    else if(qWins===3&&pWins===0){pts*=2;shoot=-1;}
  }else if(Q.foul&&!P.foul&&pWins===3){pts*=2;shoot=1;}
  else if(P.foul&&!Q.foul&&qWins===3){pts*=2;shoot=-1;}
  return {pts,detail,shoot};
}

/* ================= 玩家数据 ================= */
const DATA_FILE = path.join(__dirname,'players.json');
let players = {};            // uid -> {name,balance,games,wins,recharges:[]}
try{players=JSON.parse(fs.readFileSync(DATA_FILE,'utf8'));}catch(e){}
let dirty=false;
function saveSoon(){dirty=true;}
setInterval(()=>{if(dirty){dirty=false;
  fs.writeFile(DATA_FILE,JSON.stringify(players),()=>{});}},5000);
function getPlayer(uid,name){
  if(!players[uid])players[uid]={name:name||'玩家',balance:START_BALANCE,games:0,wins:0,recharges:[]};
  if(name)players[uid].name=name;
  return players[uid];
}

/* ================= 房间 ================= */
const rooms = {};            // code -> room
const AI_NICKS=['顺子哥','阿乐','发财仔','老K','棠妹','大旺','龙哥','阿芳','金手指','小川','胖虎','十三妹'];
function newCode(){
  let c;do{c=(''+(Math.random()*9000+1000|0));}while(rooms[c]);
  return c;
}
function makeRoom(){
  const code=newCode();
  rooms[code]={code,state:'lobby',seats:[],hands:null,deadline:0,timer:null,round:0,created:Date.now()};
  return rooms[code];
}
function roomOf(ws){return ws.meta.room?rooms[ws.meta.room]:null;}
function send(ws,obj){if(ws&&ws.readyState===WebSocket.OPEN)ws.send(JSON.stringify(obj));}
function roomView(room){
  return {code:room.code,state:room.state,round:room.round,
    hostUid:(room.seats.find(s=>!s.ai&&s.online)||{}).uid||null,
    deadline:room.deadline,
    seats:room.seats.map(s=>({name:s.name,ai:s.ai,uid:s.ai?null:s.uid,
      online:s.ai?true:s.online,submitted:!!s.evals,
      balance:s.ai?null:getPlayer(s.uid).balance}))};
}
function broadcastRoom(room){
  const view={t:'room',room:roomView(room)};
  room.seats.forEach(s=>{if(!s.ai&&s.online)send(s.ws,view);});
}
function humanCount(room){return room.seats.filter(s=>!s.ai).length;}

function startRound(room){
  // 补AI到4人
  const used=room.seats.map(s=>s.name);
  while(room.seats.length<4){
    const nick=shuffle(AI_NICKS.filter(n=>!used.includes(n)))[0]||('电脑'+room.seats.length);
    used.push(nick);
    room.seats.push({ai:true,name:nick,uid:null,ws:null,online:true,hand:null,evals:null,foul:false,arr:null});
  }
  room.state='arranging';room.round++;
  room.deadline=Date.now()+ARRANGE_MS;
  const deck=shuffle(makeDeck());
  room.seats.forEach((s,i)=>{
    s.hand=deck.slice(i*13,i*13+13);
    s.evals=null;s.foul=false;s.arr=null;
    if(s.ai){
      const best=bestArrange(s.hand);
      s.arr={front:best.front,mid:best.mid,back:best.back};
      s.evals=[evaluate3(best.front),evaluate5(best.mid),evaluate5(best.back)];
    }
  });
  broadcastRoom(room);     // 先同步座位,再发牌
  room.seats.forEach((s,i)=>{
    if(!s.ai&&s.online)send(s.ws,{t:'deal',hand:s.hand,seat:i,deadline:room.deadline,round:room.round});
  });
  clearTimeout(room.timer);
  room.timer=setTimeout(()=>settle(room),ARRANGE_MS+1000);
}
function sameCards(a,b){
  const key=c=>c.r+'-'+c.s;
  return a.map(key).sort().join()===b.map(key).sort().join();
}
function trySettle(room){
  const waiting=room.seats.some(s=>!s.ai&&s.online&&!s.evals);
  if(!waiting){clearTimeout(room.timer);settle(room);}
  else{
    const submitted=room.seats.map((s,i)=>s.evals?i:-1).filter(i=>i>=0);
    room.seats.forEach(s=>{if(!s.ai&&s.online)send(s.ws,{t:'status',submitted});});
  }
}
function settle(room){
  if(room.state!=='arranging')return;
  // 未提交者(掉线/超时)自动代摆
  room.seats.forEach(s=>{
    if(!s.evals){
      const best=bestArrange(s.hand);
      s.arr={front:best.front,mid:best.mid,back:best.back};
      s.evals=[evaluate3(best.front),evaluate5(best.mid),evaluate5(best.back)];
      s.foul=false;s.auto=true;
    }
  });
  const n=room.seats.length;
  const totals=new Array(n).fill(0);
  const pairs=[];
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    const r=scoreMatch(room.seats[i],room.seats[j]);
    totals[i]+=r.pts;totals[j]-=r.pts;
    pairs.push([i,j,r]);
  }
  room.seats.forEach((s,i)=>{
    if(!s.ai){
      const p=getPlayer(s.uid);
      p.balance+=totals[i]*COIN_PER_ROAD;
      p.games++;if(totals[i]>0)p.wins++;
      saveSoon();
    }
  });
  room.state='result';
  const payload={t:'result',
    players:room.seats.map((s,i)=>({name:s.name,ai:s.ai,foul:s.foul,auto:!!s.auto,
      front:s.arr.front,mid:s.arr.mid,back:s.arr.back,
      total:totals[i],coins:totals[i]*COIN_PER_ROAD,
      balance:s.ai?null:getPlayer(s.uid).balance})),
    pairs:pairs.map(([i,j,r])=>({i,j,pts:r.pts,detail:r.detail,shoot:r.shoot}))};
  room.seats.forEach(s=>{s.auto=false;if(!s.ai&&s.online)send(s.ws,payload);});
  broadcastRoom(room);
}
function leaveRoom(ws){
  const room=roomOf(ws);if(!room)return;
  const seat=room.seats.find(s=>!s.ai&&s.uid===ws.meta.uid);
  if(seat){
    if(room.state==='lobby'){
      room.seats=room.seats.filter(s=>s!==seat);
    }else{
      seat.online=false;seat.ws=null;   // 对局中掉线:保留座位,超时自动代摆
    }
  }
  ws.meta.room=null;
  if(!room.seats.some(s=>!s.ai&&s.online)){
    clearTimeout(room.timer);delete rooms[room.code];   // 没有真人了,销毁房间
  }else broadcastRoom(room);
}

/* ================= HTTP ================= */
const server=http.createServer((req,res)=>{
  const u=new URL(req.url,'http://x');
  if(u.pathname==='/admin'){
    if(u.searchParams.get('key')!==ADMIN_KEY){res.writeHead(403);res.end('forbidden');return;}
    const online=[...wss.clients].filter(c=>c.readyState===WebSocket.OPEN).length;
    let html='<!DOCTYPE html><meta charset="utf8"><meta http-equiv="refresh" content="10">'+
      '<title>十三张后台</title><style>body{font-family:sans-serif;background:#10241a;color:#eee;padding:20px}'+
      'table{border-collapse:collapse;margin:10px 0}td,th{border:1px solid #475;padding:5px 10px;font-size:14px}'+
      'h2{color:#ffd54a}</style>';
    html+='<h1>十三张 管理后台</h1>';
    html+='<h2>实时</h2><p>当前在线连接: <b>'+online+'</b> | 活跃房间: <b>'+Object.keys(rooms).length+'</b></p>';
    html+='<h2>房间</h2><table><tr><th>房号</th><th>状态</th><th>局数</th><th>座位</th></tr>';
    Object.values(rooms).forEach(r=>{
      html+='<tr><td>'+r.code+'</td><td>'+r.state+'</td><td>'+r.round+'</td><td>'+
        r.seats.map(s=>s.name+(s.ai?'(AI)':s.online?'':'(掉线)')).join(', ')+'</td></tr>';
    });
    html+='</table><h2>注册玩家</h2><table><tr><th>昵称</th><th>余额(金币)</th><th>≈元</th><th>局数</th><th>胜局</th><th>累计充值(元,模拟)</th></tr>';
    Object.values(players).forEach(p=>{
      const tot=p.recharges.reduce((s,r)=>s+r.yuan,0);
      html+='<tr><td>'+p.name+'</td><td>'+p.balance+'</td><td>'+(p.balance/COIN_PER_YUAN).toFixed(2)+
        '</td><td>'+p.games+'</td><td>'+p.wins+'</td><td>'+tot+'</td></tr>';
    });
    html+='</table><h2>充值记录(模拟,无真实支付)</h2><table><tr><th>时间</th><th>玩家</th><th>金额</th><th>金币</th></tr>';
    const recs=[];
    Object.values(players).forEach(p=>p.recharges.forEach(r=>recs.push({n:p.name,...r})));
    recs.sort((a,b)=>b.time-a.time).slice(0,100).forEach(r=>{
      html+='<tr><td>'+new Date(r.time).toLocaleString('zh-CN')+'</td><td>'+r.n+'</td><td>¥'+r.yuan+'</td><td>'+r.coins+'</td></tr>';
    });
    html+='</table>';
    res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});res.end(html);
    return;
  }
  // 只对外提供游戏页面本身
  if(u.pathname!=='/'&&u.pathname!=='/index.html'){res.writeHead(404);res.end('not found');return;}
  fs.readFile(path.join(__dirname,'index.html'),(err,data)=>{
    if(err){res.writeHead(404);res.end('not found');return;}
    res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});res.end(data);
  });
});

/* ================= WebSocket ================= */
const wss=new WebSocket.Server({server});
wss.on('connection',ws=>{
  ws.meta={uid:null,room:null};
  ws.on('message',raw=>{
    let m;try{m=JSON.parse(raw);}catch(e){return;}
    try{handle(ws,m);}catch(e){send(ws,{t:'error',msg:'服务器内部错误'});console.error(e);}
  });
  ws.on('close',()=>leaveRoom(ws));
});
function handle(ws,m){
  if(m.t==='hello'){
    const uid=(typeof m.uid==='string'&&m.uid.length>=8&&m.uid.length<=64)?m.uid:crypto.randomUUID();
    ws.meta.uid=uid;
    const name=(''+(m.name||'')).trim().slice(0,12);
    const p=getPlayer(uid,name||undefined);
    send(ws,{t:'welcome',uid,name:p.name,balance:p.balance});
    saveSoon();
    return;
  }
  if(!ws.meta.uid){send(ws,{t:'error',msg:'请先连接'});return;}
  const p=getPlayer(ws.meta.uid);
  if(m.t==='setname'){
    const name=(''+(m.name||'')).trim().slice(0,12);
    if(!name){send(ws,{t:'error',msg:'昵称不能为空'});return;}
    p.name=name;saveSoon();
    send(ws,{t:'nameok',name});
    const room=roomOf(ws);
    if(room){const seat=room.seats.find(s=>s.uid===ws.meta.uid);if(seat)seat.name=name;broadcastRoom(room);}
    return;
  }
  if(m.t==='create'||m.t==='join'){
    if(ws.meta.room)leaveRoom(ws);
    let room;
    if(m.t==='create')room=makeRoom();
    else{
      room=rooms[(''+m.code).trim()];
      if(!room){send(ws,{t:'error',msg:'房间不存在'});return;}
      // 断线重连:原座位还在则直接回座
      const old=room.seats.find(s=>!s.ai&&s.uid===ws.meta.uid);
      if(old){
        old.ws=ws;old.online=true;ws.meta.room=room.code;
        broadcastRoom(room);
        if(room.state==='arranging'&&!old.evals)
          send(ws,{t:'deal',hand:old.hand,seat:room.seats.indexOf(old),deadline:room.deadline,round:room.round});
        return;
      }
      if(room.state!=='lobby'){send(ws,{t:'error',msg:'该房间已开局,等下一局开始前再进'});return;}
      if(room.seats.filter(s=>!s.ai).length>=4){send(ws,{t:'error',msg:'房间已满'});return;}
    }
    room.seats.push({ai:false,uid:ws.meta.uid,name:p.name,ws,online:true,hand:null,evals:null,foul:false,arr:null});
    ws.meta.room=room.code;
    broadcastRoom(room);
    return;
  }
  const room=roomOf(ws);
  if(m.t==='leave'){leaveRoom(ws);send(ws,{t:'left'});return;}
  if(!room){send(ws,{t:'error',msg:'不在房间中'});return;}
  const seatIdx=room.seats.findIndex(s=>!s.ai&&s.uid===ws.meta.uid);
  const seat=room.seats[seatIdx];
  if(!seat){send(ws,{t:'error',msg:'不在座位上'});return;}
  seat.ws=ws;seat.online=true;
  const isHost=roomView(room).hostUid===ws.meta.uid;
  if(m.t==='start'){
    if(room.state!=='lobby'){send(ws,{t:'error',msg:'已经开局了'});return;}
    if(!isHost){send(ws,{t:'error',msg:'只有房主能开局'});return;}
    startRound(room);
    return;
  }
  if(m.t==='again'){
    if(room.state!=='result'){send(ws,{t:'error',msg:'本局还没结束'});return;}
    if(!isHost){send(ws,{t:'error',msg:'只有房主能开下一局'});return;}
    room.state='lobby';
    startRound(room);
    return;
  }
  if(m.t==='arrange'){
    if(room.state!=='arranging'){send(ws,{t:'error',msg:'现在不能提交'});return;}
    if(seat.evals){send(ws,{t:'error',msg:'已提交过'});return;}
    const c=m.cards||{};
    const front=c.front||[],mid=c.mid||[],back=c.back||[];
    if(front.length!==3||mid.length!==5||back.length!==5||
       !sameCards([...front,...mid,...back],seat.hand)){
      send(ws,{t:'error',msg:'牌不合法'});return;
    }
    const fe=evaluate3(front),me=evaluate5(mid),be=evaluate5(back);
    seat.arr={front,mid,back};
    seat.evals=[fe,me,be];
    seat.foul=!(cmpKey(be,me)>=0&&cmpKey(me,fe)>=0);
    trySettle(room);
    return;
  }
  if(m.t==='recharge'){
    const yuan=[6,30,68,98,198,328].includes(m.yuan)?m.yuan:null;
    if(!yuan){send(ws,{t:'error',msg:'金额不支持'});return;}
    const coins=yuan*COIN_PER_YUAN;
    p.balance+=coins;
    p.recharges.push({time:Date.now(),yuan,coins});
    saveSoon();
    send(ws,{t:'balance',balance:p.balance,recharged:coins});
    if(room)broadcastRoom(room);
    return;
  }
}
server.listen(PORT,()=>console.log('十三张服务器已启动: http://localhost:'+PORT+'  后台: /admin?key='+ADMIN_KEY));
