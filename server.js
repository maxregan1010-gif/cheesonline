const http=require("http"),fs=require("fs"),path=require("path"),WebSocket=require("ws");
const PORT=process.env.PORT||10000,rooms=new Map();
const START=[["br","bn","bb","bq","bk","bb","bn","br"],["bp","bp","bp","bp","bp","bp","bp","bp"],["","","","","","","",""],["","","","","","","",""],["","","","","","","",""],["","","","","","","",""],["wp","wp","wp","wp","wp","wp","wp","wp"],["wr","wn","wb","wq","wk","wb","wn","wr"]];
const files=__dirname;
const CODES="ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
const col=p=>p?p[0]:""; const inside=(r,c)=>r>=0&&r<8&&c>=0&&c<8;
function code(){let s="";for(let i=0;i<6;i++)s+=CODES[Math.floor(Math.random()*CODES.length)];return s}
function clone(x){return JSON.parse(JSON.stringify(x))}
function rawMoves(B,r,c,attacks=false){let p=B[r][c],o=[];if(!p)return o;let t=p[1],cl=p[0],add=(a,b)=>{if(inside(a,b)&&col(B[a][b])!==cl)o.push([a,b])};
 if(t==="p"){let d=cl==="w"?-1:1,start=cl==="w"?6:1;if(!attacks&&inside(r+d,c)&&!B[r+d][c]){o.push([r+d,c]);if(r===start&&!B[r+2*d][c])o.push([r+2*d,c])}for(let x of[-1,1])if(inside(r+d,c+x)&&(attacks||col(B[r+d][c+x])))add(r+d,c+x)}
 if(t==="n")for(let x of[[2,1],[2,-1],[-2,1],[-2,-1],[1,2],[1,-2],[-1,2],[-1,-2]])add(r+x[0],c+x[1]);
 if(t==="k")for(let i=-1;i<=1;i++)for(let j=-1;j<=1;j++)if(i||j)add(r+i,c+j);
 if("rbq".includes(t)){let d=[];if(t!=="b")d=[[1,0],[-1,0],[0,1],[0,-1]];if(t!=="r")d.push([1,1],[1,-1],[-1,1],[-1,-1]);for(let x of d){let a=r+x[0],b=c+x[1];while(inside(a,b)){if(!B[a][b])o.push([a,b]);else{add(a,b);break}a+=x[0];b+=x[1]}}}return o}
function attacked(B,r,c,by){for(let a=0;a<8;a++)for(let b=0;b<8;b++)if(col(B[a][b])===by&&rawMoves(B,a,b,true).some(x=>x[0]===r&&x[1]===c))return true;return false}
function kingSafe(B,color){for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(B[r][c]===color+"k")return !attacked(B,r,c,color==="w"?"b":"w");return false}
function pseudoLegal(g,r,c){
 let p=g.board[r][c],out=rawMoves(g.board,r,c,false);if(!p||p[0]!==g.turn)return [];
 if(p[1]==="p"&&g.ep&&g.ep.r===r+(p[0]==="w"?-1:1)&&Math.abs(g.ep.c-c)===1)out.push([g.ep.r,g.ep.c]);
 if(p[1]==="k"&&Math.abs(c-4)<=0&&r===(p[0]==="w"?7:0)){
  let row=r;
  if(!g.castle[p[0]].k&&g.board[row][5]===""&&g.board[row][6]===""&&g.board[row][7]===p[0]+"r"&&!attacked(g.board,row,4,p[0]==="w"?"b":"w")&&!attacked(g.board,row,5,p[0]==="w"?"b":"w")&&!attacked(g.board,row,6,p[0]==="w"?"b":"w"))out.push([row,6]);
  if(!g.castle[p[0]].q&&g.board[row][1]===""&&g.board[row][2]===""&&g.board[row][3]===""&&g.board[row][0]===p[0]+"r"&&!attacked(g.board,row,4,p[0]==="w"?"b":"w")&&!attacked(g.board,row,3,p[0]==="w"?"b":"w")&&!attacked(g.board,row,2,p[0]==="w"?"b":"w"))out.push([row,2]);
 }return out}
function legal(g,r,c){
 let p=g.board[r][c];if(!p||p[0]!==g.turn)return [];
 return pseudoLegal(g,r,c).filter(([tr,tc])=>{let h=clone(g);execute(h,r,c,tr,tc,"q",true);return kingSafe(h.board,p[0])})
}
function allMoves(g,color=g.turn){let a=[];for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(col(g.board[r][c])===color)for(let m of legal(g,r,c))a.push([r,c,m[0],m[1]]);return a}
function execute(g,fr,fc,tr,tc,promotion="q",simulation=false){
 let p=g.board[fr][fc],cl=p[0],type=p[1],capt=g.board[tr][tc];
 g.halfmove=(type==="p"||capt)?0:g.halfmove+1;
 if(type==="p"&&g.ep&&tr===g.ep.r&&tc===g.ep.c&&!capt){let cr=tr+(cl==="w"?1:-1);g.board[cr][tc]="";capt=true}
 g.board[tr][tc]=p;g.board[fr][fc]="";
 if(type==="p"&&(tr===0||tr===7))g.board[tr][tc]=cl+(["q","r","b","n"].includes(promotion)?promotion:"q");
 if(type==="k"){g.castle[cl].k=true;g.castle[cl].q=true;if(Math.abs(tc-fc)===2){if(tc===6){g.board[tr][5]=g.board[tr][7];g.board[tr][7]=""}else{g.board[tr][3]=g.board[tr][0];g.board[tr][0]=""}}}
 if(type==="r"){if(cl==="w"&&fr===7&&fc===0)g.castle.w.q=true;if(cl==="w"&&fr===7&&fc===7)g.castle.w.k=true;if(cl==="b"&&fr===0&&fc===0)g.castle.b.q=true;if(cl==="b"&&fr===0&&fc===7)g.castle.b.k=true}
 if(capt&&typeof capt==="string"&&capt[1]==="r"){let oc=capt[0];if(tr===7&&tc===0&&oc==="w")g.castle.w.q=true;if(tr===7&&tc===7&&oc==="w")g.castle.w.k=true;if(tr===0&&tc===0&&oc==="b")g.castle.b.q=true;if(tr===0&&tc===7&&oc==="b")g.castle.b.k=true}
 g.ep=null;if(type==="p"&&Math.abs(tr-fr)===2)g.ep={r:(fr+tr)/2,c:fc};
 g.turn=cl==="w"?"b":"w";g.positionCount=positionKey(g);if(!simulation)g.history.push(g.positionCount)
}
function positionKey(g){return g.board.map(r=>r.join(",")).join("/")+" "+g.turn+" "+JSON.stringify(g.castle)+" "+JSON.stringify(g.ep)}
function insufficient(g){let pieces=[];for(let r of g.board)for(let p of r)if(p&&p[1]!=="k")pieces.push(p[1]);if(!pieces.length)return true;if(pieces.every(x=>x==="b"||x==="n")){let bishops=[];for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(g.board[r][c]&&g.board[r][c][1]==="b")bishops.push((r+c)%2);if(pieces.every(x=>x==="b"))return bishops.every(x=>x===bishops[0])}return pieces.length===1&&(pieces[0]==="b"||pieces[0]==="n")}
function status(g){let moves=allMoves(g),check=!kingSafe(g.board,g.turn);if(!moves.length)return check?(g.turn==="w"?"blackMate":"whiteMate"):"stalemate";if(insufficient(g))return"insufficient";let count=g.history.filter(x=>x===g.positionCount).length;if(count>=3)return"threefold";if(g.halfmove>=100)return"fiftyMove";return check?"check":""}
function makeState(g){let now=Date.now(),w=g.clocks.w,b=g.clocks.b;if(g.running){let e=now-g.lastTick;if(g.turn==="w")w-=e;else b-=e}let st=status(g);let legal=[];if(g.started&&!g.finished&&g.players.length===2){for(let r=0;r<8;r++)for(let c=0;c<8;c++)if(col(g.board[r][c])===g.turn)for(let m of legal(g,r,c))legal.push(m)}
return{board:g.board,turn:g.turn,clocks:{w:Math.max(0,w),b:Math.max(0,b)},running:g.running,serverNow:now,gameState:st,checkColor:st==="check"?g.turn:null,legal,canClaim50:g.halfmove>=100,canClaimRep:g.history.filter(x=>x===g.positionCount).length>=3}}
function broadcast(g,msg){for(let p of g.players)if(p.ws.readyState===WebSocket.OPEN)p.ws.send(JSON.stringify(msg))}
function roomMsg(g){for(let p of g.players)p.ws.send(JSON.stringify({type:"room",code:g.code,host:p===g.host,players:g.players.map(x=>({name:x.name}))}))}
function newRoom(){let c;do{c=code()}while(rooms.has(c));let g={code:c,players:[],host:null,started:false,finished:false,running:false,turn:"w",board:clone(START),clocks:{w:300000,b:300000},lastTick:0,castle:{w:{k:false,q:false},b:{k:false,q:false}},ep:null,halfmove:0,history:[],positionCount:"",drawOffer:null};g.positionCount=positionKey(g);g.history=[g.positionCount];rooms.set(c,g);return g}
function attach(g,ws,name){if(g.players.length>=2){ws.send(JSON.stringify({type:"error",message:"این اتاق پر است."}));return null}let safe=String(name||"بازیکن").trim().replace(/\s+/g," ").slice(0,20)||"بازیکن "+(g.players.length+1);let p={ws,name:safe};g.players.push(p);ws.room=g;ws.player=p;if(!g.host)g.host=p;roomMsg(g);return p}
function start(g,p){if(p!==g.host||g.players.length!==2||g.started)return false;g.started=true;g.running=true;g.finished=false;g.lastTick=Date.now();g.players.forEach((x,i)=>x.ws.send(JSON.stringify({type:"start",color:i?"b":"w",state:makeState(g)})));return true}
function end(g,message){g.running=false;g.finished=true;broadcast(g,{type:"ended",message,state:makeState(g)})}
function leave(ws){let g=ws.room,p=ws.player;if(!g)return;g.players=g.players.filter(x=>x!==p);if(g.host===p)g.host=g.players[0]||null;if(g.players.length===0)rooms.delete(g.code);else if(g.started)broadcast(g,{type:"left",message:"بازیکن مقابل از بازی خارج شد."});else roomMsg(g)}
const server=http.createServer((req,res)=>{let f=req.url==="/"?"index.html":req.url;if(f.includes(".."))return res.writeHead(400).end();fs.readFile(path.join(files,f),(e,d)=>{if(e)return res.writeHead(404).end();res.writeHead(200,{"Content-Type":"text/html; charset=utf-8"}).end(d)})});
const wss=new WebSocket.Server({server});
wss.on("connection",ws=>ws.on("message",raw=>{let m;try{m=JSON.parse(raw)}catch{return}
 if(m.type==="create"){let g=newRoom();attach(g,ws,m.name);return}
 if(m.type==="join"){let g=rooms.get(String(m.room||"").toUpperCase());if(!g)return ws.send(JSON.stringify({type:"error",message:"اتاق پیدا نشد."}));attach(g,ws,m.name);return}
 let g=ws.room,p=ws.player;if(!g||!p)return;
 if(m.type==="start"){if(!start(g,p))ws.send(JSON.stringify({type:"error",message:"فقط میزبان و فقط با دو بازیکن می‌تواند شروع کند."}));return}
 if(m.type==="leave"){leave(ws);ws.room=null;return}
 if(m.type==="resign"){if(g.started&&!g.finished)end(g,p===g.players[0]?"🏳️ سفید تسلیم شد؛ سیاه برنده شد":"🏳️ سیاه تسلیم شد؛ سفید برنده شد");return}
 if(m.type==="drawOffer"){if(g.started&&!g.finished){g.drawOffer=p;let q=g.players.find(x=>x!==p);q?.ws.send(JSON.stringify({type:"drawOffer"}))}return}
 if(m.type==="drawAccept"){if(g.drawOffer&&g.drawOffer!==p)end(g,"🤝 مساوی با توافق دو بازیکن");return}
 if(m.type==="drawDecline"){if(g.drawOffer){let q=g.drawOffer;q.ws.send(JSON.stringify({type:"drawDeclined"}));g.drawOffer=null}return}
 if(m.type==="move"){
  if(!g.started||g.finished||g.players.length!==2)return;
  let now=Date.now();g.clocks[g.turn]-=now-g.lastTick;g.lastTick=now;if(g.clocks[g.turn]<=0)return end(g,g.turn==="w"?"⏰ زمان سفید تمام شد؛ سیاه برنده شد":"⏰ زمان سیاه تمام شد؛ سفید برنده شد");
  let color=p===g.players[0]?"w":"b";if(color!==g.turn)return;
  let {fr,fc,tr,tc,promotion}=m;if(![fr,fc,tr,tc].every(Number.isInteger)||!inside(fr,fc)||!inside(tr,tc))return;
  if(!legal(g,fr,fc).some(x=>x[0]===tr&&x[1]===tc))return;
  let piece=g.board[fr][fc],promo=promotion||"q";if(piece[1]==="p"&&(tr===0||tr===7)&&!["q","r","b","n"].includes(promo))return;
  execute(g,fr,fc,tr,tc,promo,false);let s=status(g);if(["whiteMate","blackMate","stalemate","threefold","fiftyMove","insufficient"].includes(s)){let msg=s==="stalemate"?"🤝 پات؛ بازی مساوی شد":s==="threefold"?"🤝 تساوی به دلیل تکرار سه‌باره":s==="fiftyMove"?"🤝 تساوی طبق قانون ۵۰ حرکت":s==="insufficient"?"🤝 مهره کافی برای مات وجود ندارد؛ مساوی":s==="whiteMate"?"♟️ کیش مات؛ سفید برنده شد":"♟️ کیش مات؛ سیاه برنده شد";return end(g,msg)}broadcast(g,{type:"state",state:makeState(g)})
 }
}));
setInterval(()=>{for(let g of rooms.values())if(g.running&&!g.finished){let now=Date.now();if(g.clocks[g.turn]-(now-g.lastTick)<=0){g.clocks[g.turn]=0;end(g,g.turn==="w"?"⏰ زمان سفید تمام شد؛ سیاه برنده شد":"⏰ زمان سیاه تمام شد؛ سفید برنده شد")}}},200);
server.listen(PORT,()=>console.log("Chess online server on "+PORT));