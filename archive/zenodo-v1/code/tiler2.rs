// Erdos #634 -- edge-to-edge tiling search, half-edge kernel.  v2 (correct boundary topology).
//
// Boundary = a set of DIRECTED edges, untiled region on the LEFT of each.  To seat a tile
// (CCW triangle V,A1,A2) we (1) check it lies inside the untiled region, (2) split every edge
// (boundary and the tile's three edges, taken in CW order V->A2->A1->V so the *remaining*
// untiled region is on their left) at all incident vertices, (3) cancel exact reverse pairs.
// What's left is the new boundary.  This handles T-junctions (vertex mid-edge) and the region
// closing up (edges cancel), which the v1 corner-splicer did not.
//
// Build: rustc -O tiler2.rs -o tiler2
// Tests: ./tiler2 validate         # reptiles N=4,9,16,25 -- ALL must be FOUND
//        ./tiler2 443 [limit]      # search smallest open case (only trust a FOUND tiling)

use std::time::Instant;
const EPS: f64 = 1e-7;
type P = [f64;2];
fn sub(a:P,b:P)->P{[a[0]-b[0],a[1]-b[1]]}
fn add(a:P,b:P)->P{[a[0]+b[0],a[1]+b[1]]}
fn scl(a:P,s:f64)->P{[a[0]*s,a[1]*s]}
fn dot(a:P,b:P)->f64{a[0]*b[0]+a[1]*b[1]}
fn crs(a:P,b:P)->f64{a[0]*b[1]-a[1]*b[0]}
fn nrm(a:P)->f64{dot(a,a).sqrt()}
fn dst(a:P,b:P)->f64{nrm(sub(a,b))}
fn eqp(a:P,b:P)->bool{dst(a,b)<EPS}
fn rot(v:P,t:f64)->P{let(s,c)=t.sin_cos();[v[0]*c-v[1]*s,v[0]*s+v[1]*c]}

#[derive(Clone)] struct Tile{a:f64,b:f64,c:f64,al:f64,be:f64,ga:f64}
impl Tile{
    fn new(a:f64,b:f64,c:f64)->Tile{
        let ga=2.0*std::f64::consts::PI/3.0;
        let al=(a*ga.sin()/c).asin(); let be=(b*ga.sin()/c).asin();
        Tile{a,b,c,al,be,ga}
    }
    // (phi, s1 along boundary, s2 other) for the 6 seatings.
    fn seat(&self)->Vec<(f64,f64,f64)>{
        let adj=[(self.al,self.b,self.c),(self.be,self.a,self.c),(self.ga,self.a,self.b)];
        let mut o=vec![]; for (p,x,y) in adj{o.push((p,x,y));o.push((p,y,x));} o
    }
}
type Edge=(P,P);

// point strictly on the open segment (A,B)?
fn on_seg(p:P,a:P,b:P)->bool{
    if eqp(p,a)||eqp(p,b){return false;}
    let ab=sub(b,a); let ap=sub(p,a);
    let t=dot(ap,ab)/dot(ab,ab);
    t>EPS && t<1.0-EPS && crs(ab,ap).abs() < EPS*nrm(ab).max(1.0)
}
// proper crossing of open segments (a,b) and (c,d) (not at shared/touching endpoints)
fn proper_cross(a:P,b:P,c:P,d:P)->bool{
    let d1=crs(sub(b,a),sub(c,a)); let d2=crs(sub(b,a),sub(d,a));
    let d3=crs(sub(d,c),sub(a,c)); let d4=crs(sub(d,c),sub(b,c));
    ((d1>EPS&&d2< -EPS)||(d1< -EPS&&d2>EPS)) && ((d3>EPS&&d4< -EPS)||(d3< -EPS&&d4>EPS))
}
// winding number of p w.r.t. directed edges (untiled on left). nonzero => interior.
fn winding(p:P, es:&[Edge])->i32{
    let mut w=0;
    for &(a,b) in es{
        if a[1]<=p[1]{ if b[1]>p[1] && crs(sub(b,a),sub(p,a))>0.0 {w+=1;} }
        else { if b[1]<=p[1] && crs(sub(b,a),sub(p,a))<0.0 {w-=1;} }
    }
    w
}
fn split_at(e:Edge, pts:&[P])->Vec<Edge>{
    let (a,b)=e;
    let mut mids:Vec<P>=pts.iter().cloned().filter(|&p| on_seg(p,a,b)).collect();
    mids.sort_by(|&x,&y| dst(a,x).partial_cmp(&dst(a,y)).unwrap());
    // dedup
    let mut seq=vec![a]; for m in mids{ if !eqp(*seq.last().unwrap(),m){seq.push(m);} }
    if !eqp(*seq.last().unwrap(),b){seq.push(b);}
    (0..seq.len()-1).map(|i|(seq[i],seq[i+1])).collect()
}
// place tile; return new boundary or None if invalid.
fn place(es:&[Edge], v:P,a1:P,a2:P)->Option<Vec<Edge>>{
    // validity: tile edges must not properly cross any boundary edge.
    for &(a,b) in es{
        if proper_cross(v,a2,a,b)||proper_cross(a2,a1,a,b)||proper_cross(v,a1,a,b){return None;}
    }
    // centroid must be inside untiled region
    let cen=scl(add(add(v,a1),a2),1.0/3.0);
    if winding(cen,es)==0 {return None;}
    // gather all vertices
    let mut pts:Vec<P>=Vec::new();
    for &(a,b) in es{ pts.push(a); pts.push(b);} pts.push(v);pts.push(a1);pts.push(a2);
    // split boundary + tile(CW: V->A2->A1->V) at all pts
    let mut all:Vec<Edge>=Vec::new();
    for &e in es{ all.extend(split_at(e,&pts)); }
    for &e in &[(v,a2),(a2,a1),(a1,v)]{ all.extend(split_at(*&e,&pts)); }
    // cancel exact reverse pairs
    let mut used=vec![false;all.len()];
    for i in 0..all.len(){ if used[i]{continue;}
        for j in 0..all.len(){ if used[j]||i==j{continue;}
            if eqp(all[i].0,all[j].1)&&eqp(all[i].1,all[j].0){ used[i]=true;used[j]=true;break;}
        }
    }
    let out:Vec<Edge>=(0..all.len()).filter(|&i|!used[i]).map(|i|all[i]).collect();
    // validity: every vertex equal in/out degree (forms loops); else reject
    if !degree_ok(&out){ return None; }
    Some(out)
}
fn degree_ok(es:&[Edge])->bool{
    // sum of (out-in) over a small vertex bucket must be ~0 everywhere
    let mut verts:Vec<P>=Vec::new();
    for &(a,b) in es{ for p in [a,b]{ if !verts.iter().any(|&q|eqp(q,p)){verts.push(p);} } }
    for &vx in &verts{
        let outd=es.iter().filter(|&&(a,_)|eqp(a,vx)).count() as i32;
        let ind =es.iter().filter(|&&(_,b)|eqp(b,vx)).count() as i32;
        if outd!=ind {return false;}
    }
    true
}
// extract simple loops (face on left) using clockwise-next rule at each vertex.
fn loops_of(es:&[Edge])->Vec<Vec<P>>{
    let mut rem:Vec<Edge>=es.to_vec();
    let mut out=vec![];
    while let Some(start)=rem.pop(){
        let mut loopv=vec![start.0];
        let mut cur=start;
        loop{
            loopv.push(cur.1);
            // next: outgoing edge from cur.1, choose smallest CCW angle from (cur.1->cur.0)
            let v=cur.1; let din=sub(cur.0,v);
            let mut best:Option<(usize,f64)>=None;
            for (k,&(a,b)) in rem.iter().enumerate(){
                if eqp(a,v){
                    let mut ang=sub(b,v)[1].atan2(sub(b,v)[0]) - din[1].atan2(din[0]);
                    while ang<=EPS {ang+=2.0*std::f64::consts::PI;}
                    if best.map_or(true,|(_,ba)|ang<ba){best=Some((k,ang));}
                }
            }
            match best{
                Some((k,_))=>{ cur=rem.remove(k); if eqp(cur.1,start.0){loopv.push(cur.1); break;} }
                None=>break,
            }
        }
        // close
        while loopv.len()>1 && eqp(loopv[0],*loopv.last().unwrap()){loopv.pop();}
        if loopv.len()>=3 {out.push(loopv);}
    }
    out
}
fn interior_angle(lp:&Vec<P>, i:usize)->f64{
    let n=lp.len(); let p=lp[(i+n-1)%n]; let v=lp[i]; let q=lp[(i+1)%n];
    let u1=sub(p,v); let u2=sub(q,v);
    let mut a=u1[1].atan2(u1[0]) - u2[1].atan2(u2[0]);
    while a<0.0 {a+=2.0*std::f64::consts::PI;} while a>=2.0*std::f64::consts::PI{a-=2.0*std::f64::consts::PI;}
    a
}

struct S{ t:Tile, n:usize, limit:u64, nodes:u64, found:Option<Vec<[P;3]>>, t0:Instant,
          rng:u64, maxd:usize }
impl S{
    fn rand(&mut self)->u64{ self.rng^=self.rng<<13; self.rng^=self.rng>>7; self.rng^=self.rng<<17; self.rng }
    fn dfs(&mut self, es:Vec<Edge>, placed:usize, tris:&mut Vec<[P;3]>)->bool{
        self.nodes+=1;
        if placed>self.maxd{ self.maxd=placed; }
        if self.nodes>self.limit{return false;}
        if self.nodes%2_000_000==0{ eprint!("\r nodes={}M maxdepth={}/{} t={:.0}s   ",self.nodes/1_000_000,self.maxd,self.n,self.t0.elapsed().as_secs_f64()); use std::io::Write;std::io::stderr().flush().ok(); }
        if es.is_empty(){ if placed==self.n{self.found=Some(tris.clone());return true;} return false; }
        if placed>=self.n{return false;}
        let lps=loops_of(&es);
        if lps.is_empty(){return false;}
        // most-acute corner
        let mut best=(f64::MAX,[0.0,0.0],[0.0,0.0],[0.0,0.0]); // angle, v, p(prev), q(next)
        for lp in &lps{ let m=lp.len(); for i in 0..m{
            let a=interior_angle(lp,i);
            if a<best.0{ best=(a,lp[i],lp[(i+m-1)%m],lp[(i+1)%m]); }
        }}
        let (theta,v,_p,q)=best;
        let u=scl(sub(q,v),1.0/nrm(sub(q,v)));
        let mut seats=self.t.seat();
        if self.rng!=0 { for i in (1..seats.len()).rev(){ let j=(self.rand()% (i as u64+1)) as usize; seats.swap(i,j);} }
        for (phi,s1,s2) in seats{
            if phi>theta+1e-4 {continue;}
            // s1 must fit along the boundary from v in direction u (A1 on boundary)
            let a1=add(v,scl(u,s1));
            if !self.on_boundary(a1,&es){continue;}
            let a2=add(v,scl(rot(u,phi),s2));
            if let Some(ne)=place(&es,v,a1,a2){
                tris.push([v,a1,a2]);
                if self.dfs(ne,placed+1,tris){return true;}
                tris.pop();
            }
        }
        false
    }
    fn on_boundary(&self,p:P,es:&[Edge])->bool{
        es.iter().any(|&(a,b)| eqp(p,a)||eqp(p,b)||on_seg(p,a,b))
    }
}
fn poly_area(p:&Vec<P>)->f64{let n=p.len();let mut s=0.0;for i in 0..n{s+=crs(p[i],p[(i+1)%n]);}s/2.0}
fn tri_edges(a:f64,b:f64)->Vec<Edge>{
    let s3=3.0f64.sqrt();
    let mut v=vec![[0.0,0.0],[a,0.0],[-b/2.0,b*s3/2.0]];
    if poly_area(&v)<0.0{v.reverse();}
    (0..3).map(|i|(v[i],v[(i+1)%3])).collect()
}
fn run(t:Tile, es:Vec<Edge>, n:usize, label:&str, limit:u64){ run_seed(t,es,n,label,limit,0); }
fn run_seed(t:Tile, es:Vec<Edge>, n:usize, label:&str, limit:u64, seed:u64){
    let area:f64={ let lp:Vec<P>=es.iter().map(|e|e.0).collect(); poly_area(&lp).abs() };
    let mut s=S{t,n,limit,nodes:0,found:None,t0:Instant::now(),rng:seed,maxd:0};
    let mut tr=vec![];
    let ok=s.dfs(es,0,&mut tr);
    let res=if ok{"TILING FOUND"}else if s.nodes>s.limit{"hit node limit (inconclusive)"}else{"no edge-to-edge tiling (EXHAUSTED)"};
    println!("[{}] seed={} nodes={} maxdepth={}/{} t={:.2}s -> {}",label,seed,s.nodes,s.maxd,n,s.t0.elapsed().as_secs_f64(),res);
    if let Some(tt)=&s.found{
        let tot:f64=tt.iter().map(|t|crs(sub(t[1],t[0]),sub(t[2],t[0])).abs()/2.0).sum();
        println!("   tiles={} area-sum={:.3} abc-area={:.3} ok={}",tt.len(),tot,area,(tot-area).abs()<1e-2);
    }
}
fn main(){
    let a1=std::env::args().nth(1).unwrap_or("validate".into());
    let limit:u64=std::env::args().nth(2).and_then(|s|s.parse().ok()).unwrap_or(500_000_000);
    if a1=="validate"{
        println!("== POSITIVE: reptiles must be FOUND ==");
        for m in [2.0,3.0,4.0,5.0]{
            run(Tile::new(5.0,16.0,19.0), tri_edges(5.0*m,16.0*m), (m*m) as usize, &format!("(5,16,19) m={} N={}",m,(m*m)as usize), limit);
        }
        for m in [2.0,3.0,4.0]{
            run(Tile::new(3.0,5.0,7.0), tri_edges(3.0*m,5.0*m), (m*m) as usize, &format!("(3,5,7) m={} N={}",m,(m*m)as usize), limit);
        }
        println!("== NEGATIVE: wrong N must give NO tiling ==");
        // ABC = 2*tile needs exactly 4 tiles; asking for 3 or 5 must fail.
        run(Tile::new(5.0,16.0,19.0), tri_edges(10.0,32.0), 3, "(5,16,19) 2x-region N=3 (expect none)", limit);
        run(Tile::new(5.0,16.0,19.0), tri_edges(10.0,32.0), 5, "(5,16,19) 2x-region N=5 (expect none)", limit);
        // 3*tile needs 9; asking 8 or 10 must fail.
        run(Tile::new(3.0,5.0,7.0), tri_edges(9.0,15.0), 8, "(3,5,7) 3x-region N=8 (expect none)", limit);
    } else {
        let n:usize=a1.parse().unwrap_or(443);
        let (a,b,c)=(155.0,144.0,259.0); let k=(b as f64).sqrt();
        let base=k*(2.0*b+a); let eq=k*c; let h=(eq*eq-(base/2.0).powi(2)).sqrt();
        let mut v=vec![[0.0,0.0],[base,0.0],[base/2.0,h]];
        if poly_area(&v)<0.0{v.reverse();}
        let es:Vec<Edge>=(0..3).map(|i|(v[i],v[(i+1)%3])).collect();
        let seed:u64=std::env::args().nth(3).and_then(|s|s.parse().ok()).unwrap_or(0);
        eprintln!("N={} iso ABC=({},{},{}) tile=({},{},{}) seed={}",n,eq,eq,base,a,b,c,seed);
        run_seed(Tile::new(a,b,c), es, n, &format!("N={}",n), limit, seed);
    }
}
