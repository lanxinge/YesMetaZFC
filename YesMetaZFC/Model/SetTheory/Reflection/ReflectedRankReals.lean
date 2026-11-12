import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 反坍塌两侧的真实有限求值表

真值表的每一行是已有赋值空间的子集，整表受 n×𝒫(E) 界定。
因此目标表仍在极限秩层；把表与值域界合为一个有序对后，Δ₀ 反射
实际取得壳内原表。两侧完整有限赋值真值由这些原表决定。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem fv_eval_rank_l {ω α V b A R E n L F : M.Domain}
    (hw : M.IsOmega ω) (rank : V_d I α V) (limit : M.IsLimitOrdinal α)
    (he : M.mem E V) (hn : M.mem n V)
    (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F) (space : M.IsFunctionSpace I E b A) :
    ∃ C H, M.mem C V ∧ M.mem H V ∧ Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H := by
  have pg := (program.read_l hZF hw).1
  obtain ⟨H,eval⟩ := seval_exists_l I hZF A R E F pg.2.1.1
  obtain ⟨C,power⟩ := v_power_exists_l I (ZF.modelsKP hZF) rank he
  have hc := v_power_mem_l I rank limit he power
  have rows r Y (edge : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨a,ra⟩ := (pg.2.1.2.2 r).mp ((eval.1.2.2 r).mpr ⟨Y,edge⟩)
    exact fun f hf => ((seval_row_l I hZF pg eval ra edge f).mp hf).1
  have fn : M.IsSetFunctionFromTo I H n C := ⟨eval.1.2.1,eval.1.2.2,fun r hr => by
    obtain ⟨Y,ry⟩ := (eval.1.2.2 r).mp hr
    exact ⟨Y,(power Y).mpr (rows r Y ry),ry⟩⟩
  obtain ⟨D,hd,nd,cd⟩ := v_joint_bound_l I rank hn hc
  have hh := v_relation_mem_l I rank limit hd (fun p hp => by
    obtain ⟨r,Y,pair⟩ := fn.1.1 p hp
    exact ⟨r,nd r (fn.input_mem_of_pairMember ⟨p,pair,hp⟩),Y,
      cd Y (fn.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
  exact ⟨C,H,hc,hh,fv_eval_of_l hZF hw program space eval (fn0_of_function_l (ZF.modelsKP hZF) fn)⟩

omit hZF in
def fv_pack_m {d} (b A R E n L F q : Term d) : Formula 1 d :=
  Formula.existsMem q (Formula.existsMem .newest (Formula.existsMem q.weaken.weaken
    (Formula.existsMem .newest (.conj
      (kpair0_m q.weaken.weaken.weaken.weaken (.bound 2) .newest)
      (fv_eval_m b.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
        R.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken
        L.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken (.bound 2) .newest)))))
derive_free_closed fv_pack_m

omit hZF in
theorem fv_pack_delta_l {d} (b A R E n L F q : Term d) : (fv_pack_m b A R E n L F q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (fv_eval_delta_l ..)))))

omit hZF in
theorem fv_pack_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (b A R E n L F q : Term d) :
    Formula.satisfies ρ (fv_pack_m b A R E n L F q) ↔
      ∃ C H, KPair_d M (q.eval ρ) C H ∧
        Fv_eval_d hKP (b.eval ρ) (A.eval ρ) (R.eval ρ) (E.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) C H := by
  simp only [fv_pack_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    kpair0_sat_l hKP.1,fv_eval_sat_l hKP,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  refine ⟨fun ⟨_,_,C,_,_,_,H,_,pair,eval⟩ => ⟨C,H,pair,eval⟩,?_⟩
  rintro ⟨C,H,pair,eval⟩
  obtain ⟨s,hs,hc⟩ := (kpair_union_l M pair C).mpr (Or.inl rfl)
  obtain ⟨t,ht,hh⟩ := (kpair_union_l M pair H).mpr (Or.inr rfl)
  exact ⟨s,hs,C,hc,t,ht,H,hh,pair,eval⟩

variable {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
  {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
  (hw : M.IsOmega ω) (hω : M.mem ω P)
include h hw hω

/-- 两侧求值表均实际生产，调用者不需提供任何存在或正确性占位。 -/
theorem Rf_hull_d.eval_l {b A U E n L F b' A' U' E' n' L' F' : M.Domain}
    (bb : Rd_entry_d b b' π) (aa : Rd_entry_d A A' π) (uu : Rd_entry_d U U' π)
    (ee : Rd_entry_d E E' π) (nn : Rd_entry_d n n' π) (ll : Rd_entry_d L L' π) (ff : Rd_entry_d F F' π)
    (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (space' : M.IsFunctionSpace I E' b' A') :
    ∃ C H C' H', M.mem C P ∧ M.mem H P ∧ Rd_entry_d C C' π ∧ Rd_entry_d H H' π ∧
      Fv_eval_d (ZF.modelsKP hZF) b A U E n L F C H ∧
      Fb_program_d (ZF.modelsKP hZF) ω b' n' L' F' ∧
      Fv_eval_d (ZF.modelsKP hZF) b' A' U' E' n' L' F' C' H' := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  let ρ : Env M 8 := ⟨fun i => [ω,b,A,U,E,n,L,F].get i,fun _ => ω⟩
  let η : Env M 8 := ⟨fun i => [ω,b',A',U',E',n',L',F'].get i,fun _ => ω⟩
  have images : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) π :=
    Fin.cases fixed (Fin.cases bb (Fin.cases aa (Fin.cases uu (Fin.cases ee
      (Fin.cases nn (Fin.cases ll (Fin.cases ff (fun i => Fin.elim0 i))))))))
  have tr := smap_delta_l I hZF hw h.transitive vt h.model h.target h.map
    (fb_program_m (.bound 0) (.bound 1) (.bound 5) (.bound 6) (.bound 7))
    (by simp -implicitDefEqProofs) (fb_program_delta_l ..) ρ η images
  simp only [fb_program_sat_l (ZF.modelsKP hZF)] at tr
  have program' := tr.mp program
  obtain ⟨C',H',hc',hh',eval'⟩ := fv_eval_rank_l hZF hw h.rank h.limit
    (h.map.1.1.output_mem_of_pairMember ee) (h.map.1.1.output_mem_of_pairMember nn) program' space'
  -- 用一个实际有序对同时反射表和值域界，保持存在句矩阵为 Δ₀。
  obtain ⟨s,hs,ps⟩ := sc_v_pair_l (ZF.modelsKP hZF) h.limit h.rank C' C' hc' hc'
  obtain ⟨t,ht,pt⟩ := sc_v_pair_l (ZF.modelsKP hZF) h.limit h.rank C' H' hc' hh'
  obtain ⟨q,hq,pq⟩ := sc_v_pair_l (ZF.modelsKP hZF) h.limit h.rank s t hs ht
  have pair : KPair_d M q C' H' := ⟨s,t,fun x => (ps x).trans ⟨fun e => e.elim id id,Or.inl⟩,pt,pq⟩
  let φ : Formula 1 9 := fv_pack_m (.bound 2) (.bound 3) (.bound 4) (.bound 5)
    (.bound 6) (.bound 7) (.bound 8) .newest
  have pull := h.map.exists_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ]) (fv_pack_delta_l ..) ρ η images
  simp only [φ,fv_pack_sat_l (ZF.modelsKP hZF)] at pull
  obtain ⟨p,hp,C,H,code,eval⟩ := pull.mpr ⟨q,hq,C',H',pair,eval'⟩
  have inside := code.mem_l M h.transitive hp
  obtain ⟨D,_,cd⟩ := h.map.1.1.2.2 C inside.1
  obtain ⟨J,_,hj⟩ := h.map.1.1.2.2 H inside.2
  let ρ' : Env M 10 := (ρ.push C).push H
  let η' : Env M 10 := (η.push D).push J
  have copied := smap_delta_l I hZF hw h.transitive vt h.model h.target h.map
    (fv_eval_m (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fv_eval_delta_l ..) ρ' η' (Fin.cases hj (Fin.cases cd images))
  simp only [fv_eval_sat_l (ZF.modelsKP hZF)] at copied
  exact ⟨C,H,D,J,inside.1,inside.2,cd,hj,eval,program',copied.mp eval⟩

/-- 原程序、原赋值的有限真值直接沿反坍塌传输，覆盖全部内部有限长度。 -/
theorem Rf_hull_d.finite_truth_l {b A U E n L F r f b' A' U' E' n' L' F' r' f' : M.Domain}
    (bb : Rd_entry_d b b' π) (aa : Rd_entry_d A A' π) (uu : Rd_entry_d U U' π)
    (ee : Rd_entry_d E E' π) (nn : Rd_entry_d n n' π) (ll : Rd_entry_d L L' π) (ff : Rd_entry_d F F' π)
    (rr : Rd_entry_d r r' π) (gg : Rd_entry_d f f' π)
    (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (space : M.IsFunctionSpace I E b A) (space' : M.IsFunctionSpace I E' b' A') (hr : M.mem r n) :
    Ssat_d I A U E F n r f ↔ Ssat_d I A' U' E' F' n' r' f' := by
  obtain ⟨C,H,C',H',_,_,cc,hh,eval,program',eval'⟩ := h.eval_l hZF hw hω bb aa uu ee nn ll ff program space'
  have tr := smap_delta_l I hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target h.map
    (fv_at_m (.bound 0) (.bound 1) (.bound 2) (.bound 3))
    (by simp -implicitDefEqProofs) (fv_at_delta_l ..)
    ⟨fun i => [C,H,r,f].get i,fun _ => f⟩ ⟨fun i => [C',H',r',f'].get i,fun _ => f'⟩
    (Fin.cases cc (Fin.cases hh (Fin.cases rr (Fin.cases gg (fun i => Fin.elim0 i)))))
  simp only [fv_at_sat_l hZF.1] at tr
  have hr' := (h.map.member_l I hZF hw h.model h.target rr nn).mp hr
  exact (eval.truth_l hZF hw program space hr).symm.trans
    (tr.trans (eval'.truth_l hZF hw program' space' hr'))

end YesMetaZFC.SetTheory.Internal

/-! ## 反射壳固定全部内部有限程序

指令码位于 ω×(ω×ω)，两次实际乘积给出壳内的统一值域界。
每个指令由固定数字配对而成，程序图则由内部有限函数闭包和逐值固定性恢复。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
  {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
  (hw : M.IsOmega ω)
include h hw

theorem Rf_hull_d.fixed_product_l {A B : M.Domain} (aa : Rd_entry_d A A π) (bb : Rd_entry_d B B π) :
    ∃ D, M.mem D P ∧ M.IsCartesianProduct I D A B ∧ Rd_entry_d D D π := by
  have vt := v_transitive_l I h.rank
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct hZF I A B
  have hd := ZF.v_product_mem_l I hZF h.rank h.limit
    (h.map.1.1.output_mem_of_pairMember aa) (h.map.1.1.output_mem_of_pairMember bb) prod
  let φ : Formula 1 3 := rd_graph_m .prod (.bound 1) (.bound 2) (.bound 1) .newest
  let ρ : Env M 2 := ⟨Fin.cases A (fun _ => B),fun _ => A⟩
  have tr := h.map.exists_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ]) (rd_graph_delta_l ..) ρ ρ (Fin.cases aa (fun _ => bb))
  simp only [φ,rd_graph_sat_l (ZF.modelsKP hZF)] at tr
  have read {C} : Rd_fun_d .prod A B A C ↔ M.IsCartesianProduct I C A B :=
    forall_congr' fun p => iff_congr Iff.rfl ⟨fun ⟨a,b,ha,hb,pair⟩ => ⟨a,ha,b,hb,pair⟩,
      fun ⟨a,ha,b,hb,pair⟩ => ⟨a,b,ha,hb,pair⟩⟩
  obtain ⟨C,hc,shape⟩ := tr.mpr ⟨D,hd,read.mpr prod⟩
  obtain ⟨C',_,cc⟩ := h.map.1.1.2.2 C hc
  have moved := smap_delta_l I hZF hw h.transitive vt h.model h.target h.map φ
    (by simp -implicitDefEqProofs [φ]) (rd_graph_delta_l ..) (ρ.push C) (ρ.push C')
    (Fin.cases cc (Fin.cases aa (fun _ => bb)))
  simp only [φ,rd_graph_sat_l (ZF.modelsKP hZF)] at moved
  have eq : C' = C := hZF.1.eq_of_same_members C' C (fun p => ((moved.mp shape) p).trans (shape p).symm)
  exact ⟨C,hc,read.mp shape,eq ▸ cc⟩

/-- 统一程序值域与程序本身均逐字固定，包含非标准有限程序。 -/
theorem Rf_hull_d.program_fixed_l (hω : M.mem ω P) {n F : M.Domain} (program : Sfm_d I ω n F) :
    ∃ L, M.mem L P ∧ Fn0_d n L F ∧ Rd_entry_d L L π ∧ Rd_entry_d F F π := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  obtain ⟨D,_,prod,dd⟩ := h.fixed_product_l hZF hw fixed fixed
  obtain ⟨L,hl,codes,ll⟩ := h.fixed_product_l hZF hw fixed dd
  have node {r a} (edge : Rd_entry_d r a F) : M.mem a L ∧ Rd_entry_d a a π := by
    have hr := (program.2.1.2.2 r).mpr ⟨a,edge⟩
    have rω := hw.transitive (ZF.modelsKP hZF) n program.1 r hr
    have old i (hi : M.mem i r) := hw.transitive (ZF.modelsKP hZF) r rω i hi
    have finish {j : Nat} {i z} (op : Sop_d I j a i z) (hi : M.mem i ω) (hz : M.mem z ω) :
        M.mem a L ∧ Rd_entry_d a a π := by
      obtain ⟨p,o,num,pair,code⟩ := op
      have ho := num_mem_l hZF.1 hw num
      exact ⟨(codes a).mpr ⟨o,ho,p,(prod p).mpr ⟨i,hi,z,hz,pair⟩,code⟩,
        h.pair_fixed_l hZF hw code (nat o ho) (h.pair_fixed_l hZF hw pair (nat i hi) (nat z hz))⟩
    rcases program.2.2 r a edge with ⟨i,j,op,hi,hj⟩ | ⟨i,j,op,hi,hj⟩ | ⟨i,j,op,hi,hj⟩ | ⟨i,j,op,hi,hj⟩
    · exact finish op hi hj
    · exact finish op hi hj
    · exact finish op (old i hi) (old j hj)
    · exact finish op hi (old j hj)
  have fn : M.IsSetFunctionFromTo I F n L := ⟨program.2.1.2.1,program.2.1.2.2,fun r hr => by
    obtain ⟨a,ra⟩ := (program.2.1.2.2 r).mp hr
    exact ⟨a,(node ra).1,ra⟩⟩
  have f := fn0_of_function_l (ZF.modelsKP hZF) fn
  have hf := h.finite_closed_l hZF hw hω (h.transitive L hl) program.1 f
  exact ⟨L,hl,f,ll,h.map.fixed_function_l hZF hw h.transitive vt h.model h.target (nat n program.1)
    (fun i hi => nat i (hw.transitive (ZF.modelsKP hZF) n program.1 i hi)) hl hf f (fun _ _ edge => (node edge).2)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 反坍塌在内部集合结构上的完整初等限制

任意背景完整赋值先限制到原程序的内部有限支撑。原有限图属于壳，
程序逐字固定，实际有限求值表给出两侧真值相等，再恢复完整赋值。
因此结论量化全部内部公式码，而非只量化外部标准公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 集合结构码及其关系域沿原初等图反向读取。 -/
theorem Smap_d.smdl_preimage_l {ω c d X R Y S π a A U b B W : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (ab : Rd_entry_d a b π) (aa : Rd_entry_d A B π) (uu : Rd_entry_d U W π)
    (target : Smdl_d I b B W) : Smdl_d I a A U := by
  have pair := (map.kpair_l hZF hw xt yt mx my ab aa uu).mpr target.1
  obtain ⟨z,hz⟩ := target.2.1
  have ne := map.exists_delta_l hZF hw xt yt mx my (n := 1) (.mem .newest (.bound 1))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.mem ..)
    ⟨fun _ => A,fun _ => A⟩ ⟨fun _ => B,fun _ => B⟩ (fun _ => aa)
  simp only [Formula.satisfies_mem_iff] at ne
  obtain ⟨x,_,hx⟩ := ne.mpr ⟨z,yt B (map.1.1.output_mem_of_pairMember aa) z hz,hz⟩
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := smap_delta_l I hZF hw xt yt mx my map φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases U (fun _ => A),fun _ => A⟩ ⟨Fin.cases W (fun _ => B),fun _ => B⟩ (Fin.cases uu (fun _ => aa))
  simp only [φ,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨x,y,pair⟩ := target.2.2.1 p hp
    have xy := target.2.2.2 x y ⟨p,pair,hp⟩
    exact ⟨x,xy.1,y,xy.2,pair⟩)
  refine ⟨pair,⟨x,hx⟩,fun p hp => (shape p hp).elim fun x hx => hx.2.elim fun y hy => ⟨x,y,hy.2⟩,?_⟩
  intro x y ⟨p,code,hp⟩
  obtain ⟨a,ha,b,hb,pair⟩ := shape p hp
  obtain ⟨rfl,rfl⟩ := kpair_injective_l M pair code
  exact ⟨ha,hb⟩

/-- 实际隶属关系与传递载体同时从像恢复。 -/
theorem Smap_d.smem_preimage_l {ω c d X R Y S π a A U b B W : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (ab : Rd_entry_d a b π) (aa : Rd_entry_d A B π) (uu : Rd_entry_d U W π)
    (target : Smem_d I b B W) (bt : M.TransitiveSet B) : Smem_d I a A U ∧ M.TransitiveSet A := by
  have source := map.smdl_preimage_l hZF hw xt yt mx my ab aa uu target.1
  have tr := smap_delta_l I hZF hw xt yt mx my map (n := 1)
    (Formula.forallMem .newest (Formula.subset .newest (.bound 1)))
    (by simp -implicitDefEqProofs) (.forallMem _ (.atom ..))
    ⟨fun _ => A,fun _ => A⟩ ⟨fun _ => B,fun _ => B⟩ (fun _ => aa)
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_subset_iff] at tr
  refine ⟨⟨source,fun x y => ?_⟩,tr.mpr bt⟩
  have compare (hx : M.mem x A) (hy : M.mem y A) : Rd_entry_d x y U ↔ M.mem x y := by
    obtain ⟨x',_,xx⟩ := map.1.1.2.2 x (xt A (map.1.1.input_mem_of_pairMember aa) x hx)
    obtain ⟨y',_,yy⟩ := map.1.1.2.2 y (xt A (map.1.1.input_mem_of_pairMember aa) y hy)
    have hx' := (map.member_l I hZF hw mx my xx aa).mp hx
    have hy' := (map.member_l I hZF hw mx my yy aa).mp hy
    exact (map.entry_l hZF hw xt yt mx my xx yy uu).trans
      ((target.2 x' y').trans ((and_iff_right hx').trans ((and_iff_right hy').trans
        (map.member_l I hZF hw mx my xx yy).symm)))
  exact ⟨fun edge => ⟨(source.2.2.2 x y edge).1,(source.2.2.2 x y edge).2,
    (compare (source.2.2.2 x y edge).1 (source.2.2.2 x y edge).2).mp edge⟩,
    fun ⟨hx,hy,mem⟩ => (compare hx hy).mpr mem⟩

/-- 原函数性及完整定义域由像恢复；不要求源壳存在值域集合。 -/
theorem Smap_d.function_preimage_l {ω c d X R Y S π A B f g : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (ab : Rd_entry_d A B π) (fg : Rd_entry_d f g π)
    (fn : M.IsSetFunction I g) (dom : M.IsDomainOf I B g) :
    M.IsSetFunction I f ∧ M.IsDomainOf I A f := by
  have hf := map.1.1.input_mem_of_pairMember fg
  have bounds {x y} (edge : Rd_entry_d x y f) : M.mem x X ∧ M.mem y X := by
    obtain ⟨p,pair,hp⟩ := edge
    exact pair.mem_l M xt (xt f hf p hp)
  have relation : M.IsSetRelation I f := by
    intro p hp
    obtain ⟨q,_,pq⟩ := map.1.1.2.2 p (xt f hf p hp)
    obtain ⟨x,y,pair⟩ := fn.1 q ((map.member_l I hZF hw mx my pq fg).mp hp)
    obtain ⟨a,b,_,_,code,_,_⟩ := map.kpair_preimage_l hZF hw xt yt mx my pq pair
    exact ⟨a,b,code⟩
  refine ⟨⟨relation,?_⟩,fun x => ⟨?_,?_⟩⟩
  · intro x y z xy xz
    obtain ⟨x',_,xx⟩ := map.1.1.2.2 x (bounds xy).1
    obtain ⟨y',_,yy⟩ := map.1.1.2.2 y (bounds xy).2
    obtain ⟨z',_,zz⟩ := map.1.1.2.2 z (bounds xz).2
    have eq := fn.2 x' y' z' ((map.entry_l hZF hw xt yt mx my xx yy fg).mp xy)
      ((map.entry_l hZF hw xt yt mx my xx zz fg).mp xz)
    exact map.1.2 y z z' (eq ▸ yy) zz
  · intro hx
    obtain ⟨x',_,xx⟩ := map.1.1.2.2 x (xt A (map.1.1.input_mem_of_pairMember ab) x hx)
    obtain ⟨y,xy⟩ := (dom x').mp ((map.member_l I hZF hw mx my xx ab).mp hx)
    obtain ⟨z,xz,_⟩ := map.value_preimage_l hZF hw xt yt mx my xx fg fn xy
    exact ⟨z,xz⟩
  · rintro ⟨y,xy⟩
    obtain ⟨x',_,xx⟩ := map.1.1.2.2 x (bounds xy).1
    obtain ⟨y',_,yy⟩ := map.1.1.2.2 y (bounds xy).2
    exact (map.member_l I hZF hw mx my xx ab).mpr
      ((dom x').mpr ⟨y',(map.entry_l hZF hw xt yt mx my xx yy fg).mp xy⟩)

theorem Rf_hull_d.restrict_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P) {a A U b B W : M.Domain}
    (source : Smdl_d I a A U) (target : Smdl_d I b B W)
    (aa : Rd_entry_d A B π) (uu : Rd_entry_d U W π) :
    ∃ j, Smap_d I ω a b A B j ∧ M.IsRestrictionOf I j π A := by
  have vt := v_transitive_l I h.rank
  have sub := h.transitive A (h.map.1.1.input_mem_of_pairMember aa)
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  obtain ⟨j,cut⟩ := ZF.exists_restriction hZF I π A
  have initial := cut.isSetFunctionFromTo h.map.1.1 sub
  have fn : M.IsSetFunctionFromTo I j A B := ⟨initial.1,initial.2.1,fun x hx => by
    obtain ⟨y,_,xy⟩ := initial.2.2 x hx
    exact ⟨y,(h.map.member_l I hZF hw h.model h.target ((cut.2 x y).mp xy).2 aa).mp hx,xy⟩⟩
  have inj : M.IsSetInjectionFromTo I j A B := ⟨fn,fun x y z xz yz =>
    h.map.1.2 x y z ((cut.2 x z).mp xz).2 ((cut.2 y z).mp yz).2⟩
  obtain ⟨C,codes⟩ := scode_exists_l I hZF hw
  refine ⟨j,⟨inj,C,codes,?_⟩,cut⟩
  intro q f g hq hf hg assign
  obtain ⟨n,F,r,code,program,hr⟩ := (codes q).mp hq
  obtain ⟨m,hm,bound⟩ := sbound_exists_l I hZF hw program
  have mn := hw.transitive (ZF.modelsKP hZF) m hm
  obtain ⟨L,_,fl,ll,ff⟩ := h.program_fixed_l hZF hw hω program
  have pg := fb_program_of_l (ZF.modelsKP hZF) program hm bound fl
  obtain ⟨E,E',_,ee,space,space'⟩ := h.finite_space_l hZF hw hω hm aa
  obtain ⟨s,restrict⟩ := ZF.exists_restriction hZF I f m
  have sf := restrict.isSetFunctionFromTo hf mn
  have sn := fn0_of_function_l (ZF.modelsKP hZF) sf
  have hs := h.finite_closed_l hZF hw hω sub hm sn
  obtain ⟨s',_,ss⟩ := h.map.1.1.2.2 s hs
  have sn' := (h.map.function_l hZF hw h.transitive vt h.model h.target (nat m hm) aa ss).mp sn
  have sf' := fn0_function_l (ZF.modelsKP hZF) sn'
  have agree : Senv_agree_d I m f s := fun i x hi =>
    ⟨fun edge => (restrict.2 i x).mpr ⟨hi,edge⟩,fun edge => ((restrict.2 i x).mp edge).2⟩
  have agree' : Senv_agree_d I m g s' := by
    intro i y hi
    obtain ⟨x,hx,ix⟩ := sf.2.2 i hi
    obtain ⟨z,_,xz⟩ := fn.2.2 x hx
    have iz := assign i (mn i hi) x z ((restrict.2 i x).mp ix).2 xz
    have iz' := (h.map.entry_l hZF hw h.transitive vt h.model h.target
      (nat i (mn i hi)) ((cut.2 x z).mp xz).2 ss).mp ix
    exact ⟨fun iy => hg.1.2 i z y iz iy ▸ iz',fun iy => sf'.1.2 i z y iz' iy ▸ iz⟩
  have truth := h.finite_truth_l hZF hw hω (nat m hm) aa uu ee (nat n program.1) ll ff
    (nat r (hw.transitive (ZF.modelsKP hZF) n program.1 r hr)) ss pg space space' hr
  obtain ⟨D,fullA⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨D',fullB⟩ := ZF.exists_functionSpace hZF I ω B
  have left := ssat_spaces_l I hZF (R := U) program bound fullA space mn (fun _ hi => hi)
    hr ((fullA f).mpr hf) ((space s).mpr sf) agree
  have right := ssat_spaces_l I hZF (R := W) program bound fullB space' mn (fun _ hi => hi)
    hr ((fullB g).mpr hg) ((space' s').mpr sf') agree'
  have formula : Sformula_d I ω q n F r := ⟨code,program,hr⟩
  exact (satisfies_decode_l I hZF.1 source formula fullA).trans
    (left.trans (truth.trans (right.symm.trans (satisfies_decode_l I hZF.1 target formula fullB).symm)))

end YesMetaZFC.SetTheory.Internal

/-! ## 原返回秩层包含测试壳的全部实数集

秩层中已有自然数平方，故其全部背景实数都属于该秩层。内部函数空间
因此就是背景完整函数空间。反坍塌识别测试壳实数集的像，再反映其隶属关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smem_rank_reals_l {c Z R θ ω : M.Domain} (model : Smem_d I c Z R)
    (rank : V_d I θ Z) (native : (smdl_structure_l I (R := R) model.1.2.1).Models ZF)
    (hω : M.mem ω Z) : ∃ B, M.mem B Z ∧ ∀ x, M.mem x B ↔ Fn0_d ω ω x := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let Ω : N.Domain := ⟨ω,hω⟩
  have zt := v_transitive_l I rank
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I model zt
  obtain ⟨D,prod⟩ := ZF.exists_cartesianProduct native (kp_pair_l (ZF.modelsKP native)) Ω Ω
  have product := image_product_l (M := N) (N := M) (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF))
    Subtype.val inj full prod
  have real_mem x (fx : Fn0_d ω ω x) : M.mem x Z := v_subset_mem_l I rank D.property (fun p hp => by
    obtain ⟨a,ha,b,hb,pair⟩ := fx.1 p hp
    exact (product p).mpr ⟨a,ha,b,hb,pair⟩)
  obtain ⟨B,space⟩ := ZF.exists_functionSpace native (kp_pair_l (ZF.modelsKP native)) Ω Ω
  refine ⟨B.val,B.property,fun x => ⟨?_,?_⟩⟩
  · intro hx
    let x₀ : N.Domain := ⟨x,zt B.val B.property x hx⟩
    exact (smem_fn0_l I hZF.1 model zt Ω Ω x₀).mp (fn0_of_function_l (ZF.modelsKP native)
      ((space x₀).mp ((smem_member_l I model.1 model.2 x₀ B).mpr hx)))
  · intro fx
    let x₀ : N.Domain := ⟨x,real_mem x fx⟩
    exact (smem_member_l I model.1 model.2 x₀ B).mp ((space x₀).mpr
      (fn0_function_l (ZF.modelsKP native) ((smem_fn0_l I hZF.1 model zt Ω Ω x₀).mpr fx)))

theorem Rf_hull_d.reals_in_rank_l {ω T α V d Q P c R π a Y S b Z U θ B : M.Domain}
    {Φ : List Lr_formula} {n} {v : Fin n → M.Domain}
    (h : Rf_hull_d hZF ω T Φ v α V d Q P c R π) (hw : M.IsOmega ω) (hω : M.mem ω P)
    (source : Smem_d I a Y S)
    (native : (smdl_structure_l I (R := S) source.1.2.1).Models ZF) (hωY : M.mem ω Y)
    (target : Smem_d I b Z U) (rank : V_d I θ Z)
    (domain : Rd_entry_d Y Z π) (relation : Rd_entry_d S U π)
    (hB : M.mem B P) (reals : Rb_reals_d P ω B) : M.mem B Y := by
  have vt := v_transitive_l I h.rank
  have fixed := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have hωZ := (h.map.member_l I hZF hw h.model h.target fixed domain).mp hωY
  obtain ⟨j,map,_⟩ := h.restrict_l hZF hw hω source.1 target.1 domain relation
  have hZ := map.native_models_l hZF hw source.1 target.1 native
  obtain ⟨C,hC,space⟩ := smem_rank_reals_l hZF target rank hZ hωZ
  obtain ⟨D,hD,bd⟩ := h.map.1.1.2.2 B hB
  let φ : Formula 1 3 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 2) (.bound 2) .newest)
  have tr := h.map.forall_delta_l hZF hw h.transitive vt h.model h.target φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) (.iff (.mem ..) (fn0_delta_l ..))
    ⟨Fin.cases B (fun _ => ω),fun _ => ω⟩ ⟨Fin.cases D (fun _ => ω),fun _ => ω⟩ (Fin.cases bd (fun _ => fixed))
  simp only [φ,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun x hx => (reals x).trans (and_iff_right hx))
  have eq : D = C := hZF.1.eq_of_same_members D C (fun x => ⟨
    fun hx => (space x).mpr ((read x (vt D hD x hx)).mp hx),
    fun hx => (read x (vt Z (h.map.1.1.output_mem_of_pairMember domain) x
      ((v_transitive_l I rank) C hC x hx))).mpr ((space x).mp hx)⟩)
  exact (h.map.member_l I hZF hw h.model h.target (eq ▸ bd) domain).mpr hC

end YesMetaZFC.SetTheory.Internal
