import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.Model.Forcing.Collapse.ProductFilterExtension
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.ReturnOrder

/-! # 吸收后继延长每个原已接受条件

原根图固定整个旧前缀条件域及其中每个条件。把旧前缀搬到新模型后，
新前缀的任一已接受末坐标可接在任意旧已接受条件之后。所得加强仍在真实新滤子中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_filter_extend_l {ω cY Y f : M.Domain} {v w : Fin 14 → M.Domain}
    (hw : M.IsOmega ω) (left : Ab_frame_d I ω cY Y v) (right : Ab_frame_d I ω cY Y w)
    (map : Smap_d I ω (v 0) (w 0) (v 1) (w 1) f)
    (alphabet : Rd_entry_d (v 4) (w 4) f) (stage : M.SuccessorOf (w 7) (v 7))
    (preserve : M.IsRestrictionOf I (v 10) (w 10) (v 7))
    (points : ∀ q, M.mem q (v 8) → Rd_entry_d q q f) :
    ∀ q, M.mem q (v 11) → ∃ r, M.mem r (w 11) ∧ Rd_entry_d r q (w 6) := by
  let A := smdl_structure_l I (R := v 2) left.model.1.2.1
  let B := smdl_structure_l I (R := w 2) right.model.1.2.1
  have hA := ZFC.models_zf_l (left.theory.native_l I hZF hw)
  have hB := ZFC.models_zf_l (right.theory.native_l I hZF hw)
  let ω₀ : A.Domain := ⟨ω,left.inside.1⟩
  let a₀ : A.Domain := ⟨v 4,left.inside.2.1⟩
  let p₀ : A.Domain := ⟨v 5,left.inside.2.2.1⟩
  let u₀ : A.Domain := ⟨v 6,left.inside.2.2.2.1⟩
  let n₀ : A.Domain := ⟨v 7,left.inside.2.2.2.2.1⟩
  let c₀ : A.Domain := ⟨v 8,left.inside.2.2.2.2.2.1⟩
  let t₀ : A.Domain := ⟨v 9,left.inside.2.2.2.2.2.2.1⟩
  let ω₁ : B.Domain := ⟨ω,right.inside.1⟩
  let a₁ : B.Domain := ⟨w 4,right.inside.2.1⟩
  let p₁ : B.Domain := ⟨w 5,right.inside.2.2.1⟩
  let u₁ : B.Domain := ⟨w 6,right.inside.2.2.2.1⟩
  let n₁ : B.Domain := ⟨w 7,right.inside.2.2.2.2.1⟩
  let c₁ : B.Domain := ⟨w 8,right.inside.2.2.2.2.2.1⟩
  let t₁ : B.Domain := ⟨w 9,right.inside.2.2.2.2.2.2.1⟩
  obtain ⟨_,_,_,front⟩ := (ab_kernel_read_l I left.model left.transitive hA ω₀ a₀ p₀ u₀ n₀ c₀ t₀).mp left.kernel
  obtain ⟨hw₁,_,product',stage'⟩ := (ab_kernel_read_l I right.model right.transitive hB ω₁ a₁ p₁ u₁ n₁ c₁ t₁).mp right.kernel
  obtain ⟨e,elem,values⟩ := map.project_l I hZF hw left.model.1 right.model.1
  have ew : e ω₀ = ω₁ := Subtype.ext (map.1.1.1.2 _ _ _ (values ω₀)
    (map.omega_l I hZF hw left.transitive right.transitive left.model right.model left.inside.1))
  have ea : e a₀ = a₁ := Subtype.ext (map.1.1.1.2 _ _ _ (values a₀) alphabet)
  have en : (e n₀).val = v 7 := map.1.1.1.2 _ _ _ (values n₀)
    (map.natural_l hZF hw left.transitive right.transitive left.model right.model left.inside.1 _ left.index)
  have moved := fp_prefix_image_l hA hB e elem front
  rw [ew,ea] at moved
  have inj : Function.Injective (Subtype.val : B.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I right.model right.transitive
  have entry := image_entry_iff_l (M := B) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP hB)) hZF.1
  have mem {a b : B.Domain} : M.mem a.val b.val ↔ B.mem a b := image_member_l (M := B) (N := M) Subtype.val inj full
  have hn : B.mem (e n₀) ω₁ := mem.mp (en.symm ▸ left.index)
  have hm : B.mem n₁ ω₁ := mem.mp right.index
  have succ : B.SuccessorOf n₁ (e n₀) :=
    (image_successor_iff_l (ZF.modelsKP hB) hZF.1 Subtype.val inj full).mpr (en.symm ▸ stage)
  obtain ⟨t,ht⟩ := right.generic.inhabited
  have accepted := (right.accepted t).mp ht
  let t' : B.Domain := ⟨t,right.transitive _ c₁.property t accepted.1⟩
  have ft := (stage'.conditions t').mp (mem.mp accepted.1)
  intro q hq
  have saved := (left.accepted q).mp hq
  let q' : A.Domain := ⟨q,left.transitive _ c₀.property q saved.1⟩
  have qc : A.mem q' c₀ := (left.model.2 q (v 8)).mpr ⟨q'.property,c₀.property,saved.1⟩
  have eq : (e q').val = q := map.1.1.1.2 _ _ _ (values q') (points q saved.1)
  have fq := (moved.conditions (e q')).mp ((em_member_l e elem q' c₀).mp qc)
  have keep : M.IsRestrictionOf I (v 10) (w 10) (e n₀).val := by
    rw [en]
    exact preserve
  have ready₀ : Fp_ready_d I (e n₀).val (v 10) (e q').val := by
    rw [en,eq]
    exact saved.2
  obtain ⟨r,fr,ready,le⟩ := fp_ground_extend_l hB hZF Subtype.val inj full hw₁ hn hm succ fq ft
    right.function keep ready₀ accepted.2
  exact ⟨r.val,(right.accepted r.val).mpr ⟨mem.mpr ((stage'.conditions r).mpr fr),ready⟩,
    eq ▸ (entry r (e q') u₁).mp ((product'.order r (e q')).mpr
      ⟨(product'.conditions r).mpr ⟨n₁,hm,fr⟩,(product'.conditions (e q')).mpr ⟨e n₀,hn,fq⟩,le⟩)⟩

/-- 每个实际前缀滤子在全乘积中非空且有向。 -/
theorem Ab_frame_d.filter_data_l {ω cY Y : M.Domain} {v : Fin 14 → M.Domain}
    (hw : M.IsOmega ω) (h : Ab_frame_d I ω cY Y v) :
    M.MemberSubset (v 11) (v 5) ∧ ∀ p q, M.mem p (v 11) → M.mem q (v 11) →
      ∃ r, M.mem r (v 11) ∧ Rd_entry_d r p (v 6) ∧ Rd_entry_d r q (v 6) := by
  let N := smdl_structure_l I (R := v 2) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  let w : N.Domain := ⟨ω,h.inside.1⟩
  let A : N.Domain := ⟨v 4,h.inside.2.1⟩
  let P : N.Domain := ⟨v 5,h.inside.2.2.1⟩
  let U : N.Domain := ⟨v 6,h.inside.2.2.2.1⟩
  let n : N.Domain := ⟨v 7,h.inside.2.2.2.2.1⟩
  let C : N.Domain := ⟨v 8,h.inside.2.2.2.2.2.1⟩
  let T : N.Domain := ⟨v 9,h.inside.2.2.2.2.2.2.1⟩
  obtain ⟨_,_,product,stage⟩ := (ab_kernel_read_l I h.model h.transitive native w A P U n C T).mp h.kernel
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I h.model h.transitive
  have mem {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  have inside p (hp : M.mem p (v 11)) := h.transitive (v 8) C.property p ((h.accepted p).mp hp).1
  have sub p (hp : M.mem p (v 11)) : M.mem p (v 5) := by
    let p₀ : N.Domain := ⟨p,inside p hp⟩
    exact mem.mpr ((product.conditions p₀).mpr ⟨n,mem.mp h.index,(stage.conditions p₀).mp (mem.mp ((h.accepted p).mp hp).1)⟩)
  refine ⟨sub,fun p q hp hq => ?_⟩
  obtain ⟨r,hr,rp,rq⟩ := h.generic.directed p q hp hq
  have order a b (ha : M.mem a (v 11)) (hb : M.mem b (v 11)) (ab : Rd_entry_d a b (v 9)) : Rd_entry_d a b (v 6) := by
    let a₀ : N.Domain := ⟨a,inside a ha⟩
    let b₀ : N.Domain := ⟨b,inside b hb⟩
    exact (entry a₀ b₀ U).mp ((product.order a₀ b₀).mpr
      ⟨mem.mp (sub a ha),mem.mp (sub b hb),((stage.order a₀ b₀).mp ((entry a₀ b₀ T).mpr ab)).2.2⟩)
  exact ⟨r,hr,order r p hr hp rp,order r q hr hq rq⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原已接受条件在任意后来行都有返回像的加强

后继用真实末坐标延长条件；返回三角形把新的加强与原条件比较。
归纳中的存在量词仅涉及原记录、原滤子和原返回图，故适用于内部任意轮数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原生成元属于同一返回条件域；只消费真实行帧和返回条目。 -/
theorem Ab_run_d.returned_condition_l {P ω cY Y S F C U i r p q : M.Domain}
    {v : Fin 26 → M.Domain} (hw : M.IsOmega ω)
    (run : Ab_run_d I P ω cY Y S F) (ctx : Ab_return_order_d F C U)
    (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r)
    (hp : M.mem p (v 11)) (pq : Rd_entry_d p q (v 3)) : M.mem q C := by
  have frame := (run.queues i r v ir vr).frame
  exact (frame.returns.member_l I hZF hw frame.model run.target pq (ctx.rows i r v ir vr).1).mp
    ((frame.filter_data_l hZF hw).1 p hp)

theorem Ab_run_d.advance_l {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F b r₀ q E : M.Domain} {v₀ : Fin 26 → M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val)
    (start : Rd_entry_d b r₀ F) (tuple₀ : Rt_tuple_d v₀ r₀)
    (hq : M.mem q (v₀ 11)) (returned : Rd_entry_d q E (v₀ 3)) :
    ∀ j r (v : Fin 26 → M.Domain), Rd_entry_d j r F → Rt_tuple_d v r → (b = j ∨ M.mem b j) →
      ∃ p z, M.mem p (v 11) ∧ Rd_entry_d p z (v 3) ∧ Rd_entry_d z E U.val := by
  have EC := run.returned_condition_l hZF hΩ ctx start tuple₀ hq returned
  let ρ : Env M 4 := ⟨fun k => [F,b,E,U.val].get k,fun _ => F⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪∀ r H σ,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term 5)⌝ₛ,r,⌜(.bound 1 : Term 5)⌝ₛ) →
    ⌜(rt_coord_m (11 : Fin 26))⌝ₚ(r,H) → ⌜(rt_coord_m (3 : Fin 26))⌝ₚ(r,σ) →
    (⌜(.bound 2 : Term 5)⌝ₛ = ⌜(.bound 0 : Term 5)⌝ₛ ∨ ⌜(.bound 2 : Term 5)⌝ₛ ∈ ⌜(.bound 0 : Term 5)⌝ₛ) →
      ∃ p z, p ∈ H ∧ ⌜rd_entry0_m⌝ₚ(p,z,σ) ∧ ⌜rd_entry0_m⌝ₚ(z,⌜(.bound 3 : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ)⟫ }
  have read j : φ.denote ρ j ↔ ∀ r H σ, Rd_entry_d j r F → Rt_coord_d (11 : Fin 26) r H →
      Rt_coord_d (3 : Fin 26) r σ → (b = j ∨ M.mem b j) →
        ∃ p z, M.mem p H ∧ Rd_entry_d p z σ ∧ Rd_entry_d z E U.val := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all j : φ.denote ρ j := ZF.mem_ind_l M hZF I φ ρ (by
    intro j ih
    apply (read j).mpr
    intro r H σ jr cH cσ above
    obtain ⟨v,vr,code,ret,_⟩ := run.columns_l hZF.1 model trans jr
    have frame := (run.queues j r v jr vr).frame
    have coord {k : Fin 26} {x : M.Domain} (cx : Rt_coord_d k r x) : v k = x := by
      obtain ⟨w,wr,eq⟩ := cx
      exact (congrFun (rt_tuple_inj_l vr wr) k).trans eq
    have eH := coord cH
    have eσ := coord cσ
    have result : ∃ p z, M.mem p (v 11) ∧ Rd_entry_d p z (v 3) ∧ Rd_entry_d z E U.val := by
      rcases above with eq | bj
      · have rr := (fn0_function_l (ZF.modelsKP hZF) run.function).1.2 j r r₀ jr (eq ▸ start)
        have ev := rt_tuple_inj_l vr (rr.symm ▸ tuple₀)
        exact ⟨q,E,ev.symm ▸ hq,ev.symm ▸ returned,ctx.order.refl E EC⟩
      · obtain ⟨i,hi,succ⟩ := hΩ.exists_predecessor_of_mem_of_nonempty hZF (run.function.bound_l jr).1 ⟨b,bj⟩
        obtain ⟨s,_,is⟩ := run.function.2.1 i hi
        obtain ⟨w,ws,oldCode,oldReturn,_⟩ := run.columns_l hZF.1 model trans is
        have old := (run.queues i s w is ws).frame
        have bi : b = i ∨ M.mem b i := ((succ b).mp bj).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members b i eq))
        obtain ⟨p,z,hp,pz,zE⟩ := (read i).mp (ih i succ.predecessor_mem) s (w 11) (w 3) is
          ⟨w,ws,rfl⟩ ⟨w,ws,rfl⟩ bi
        obtain ⟨f,edge,_,_,alphabet,stage,preserve,points,_⟩ := run.step_links_l hZF.1 model trans succ is jr ws vr
        have keep := run.keep_l hZF.1 model trans succ is jr ws vr
        have hist := run.histories j r v jr vr
        have map := hist.diagram.elementary i j f (w 0) (w 1) (w 2) (v 0) (v 1) (v 2)
          edge (keep.1 i (w 0) oldCode) code old.model.1 frame.model.1
        have square := hist.returns.comp_l hZF hist.diagram (fun _ h => h) edge
          (keep.2.2 i (w 3) oldReturn) ret
        obtain ⟨p',hp',le⟩ := ab_filter_extend_l hZF hΩ old frame map alphabet stage ⟨old.function.1,preserve⟩ points p hp
        have fixed := points p ((old.accepted p).mp hp).1
        obtain ⟨p'',pp'',image⟩ := (square.2 p z).mp pz
        have pz' : Rd_entry_d p z (v 3) := map.1.1.1.2 _ _ _ pp'' fixed ▸ image
        have inside := frame.transitive _ frame.inside.2.2.2.2.2.1 p' ((frame.accepted p').mp hp').1
        obtain ⟨z',_,pz'₀⟩ := frame.returns.1.1.2.2 p' inside
        have zz := (frame.returns.entry_l hZF hΩ frame.transitive run.transitive frame.model run.target
          pz'₀ pz' (ctx.rows j r v jr vr).2).mp le
        exact ⟨p',z',hp',pz'₀,ctx.order.trans z' z E
          (run.returned_condition_l hZF hΩ ctx jr vr hp' pz'₀)
          (run.returned_condition_l hZF hΩ ctx is ws hp pz) EC zz zE⟩
    obtain ⟨p,z,hp,pz,zE⟩ := result
    exact ⟨p,z,eH ▸ hp,eσ ▸ pz,zE⟩) j
  exact fun j r v jr vr above => (read j).mp (all j) r (v 11) (v 3) jr ⟨v,vr,rfl⟩ ⟨v,vr,rfl⟩ above

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原前缀滤子的返回像生成同一个实际滤子

生成元是原运行各行已接受条件的原返回像。任意两个生成元在同一较晚行
取得共同加强；分离其向上闭包给出真实集合，且共同加强仍可取为原生成元。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Ab_gen_d (F q : M.Domain) : Prop := ∃ i r H σ p, Rd_entry_d i r F ∧
  Rt_coord_d (11 : Fin 26) r H ∧ Rt_coord_d (3 : Fin 26) r σ ∧ M.mem p H ∧ Rd_entry_d p q σ

def ab_gen_m {n} (F q : Term n) : Formula 1 n := set[n] ⟪∃ i r H σ p,
  ⌜rd_entry0_m⌝ₚ(i,r,⌜F⌝ₛ) ∧ ⌜(rt_coord_m (11 : Fin 26))⌝ₚ(r,H) ∧
  ⌜(rt_coord_m (3 : Fin 26))⌝ₚ(r,σ) ∧ p ∈ H ∧ ⌜rd_entry0_m⌝ₚ(p,⌜q⌝ₛ,σ)⟫
derive_free_closed ab_gen_m

theorem ab_gen_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F q : Term n) :
    Formula.satisfies ρ (ab_gen_m F q) ↔ Ab_gen_d (F.eval ρ) (q.eval ρ) := by
  simp only [ab_gen_m,Ab_gen_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,rt_coord_sat_l hE,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  rfl

structure Ab_filter_d (F C U H : M.Domain) : Prop where
  members : ∀ q, M.mem q H ↔ M.mem q C ∧ ∃ p, Ab_gen_d F p ∧ Rd_entry_d p q U
  inhabited : ∃ p, Ab_gen_d F p ∧ M.mem p H
  proper : ∀ p, M.mem p H → M.mem p C ∧ p ≠ C
  upward : ∀ p q, M.mem p H → M.mem q C → Rd_entry_d p q U → M.mem q H
  directed : ∀ p q, M.mem p H → M.mem q H → ∃ r, Ab_gen_d F r ∧ M.mem r H ∧ Rd_entry_d r p U ∧ Rd_entry_d r q U

/-- 生成元直接读取原记录坐标，不需要测试模型的内部理论。 -/
theorem Ab_gen_d.read_l {F q : M.Domain} (gen : Ab_gen_d F q) :
    ∃ i r, ∃ v : Fin 26 → M.Domain, ∃ p,
      Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ M.mem p (v 11) ∧ Rd_entry_d p q (v 3) := by
  obtain ⟨i,r,H,σ,p,ir,⟨v,vr,eH⟩,⟨w,wr,eσ⟩,hp,pq⟩ := gen
  have eq := (congrFun (rt_tuple_inj_l vr wr) 3).trans eσ
  exact ⟨i,r,v,p,ir,vr,eH.symm ▸ hp,eq.symm ▸ pq⟩

variable (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_run_d.filter_l {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val) :
    ∃ H, Ab_filter_d F C.val U.val H := by
  have generated {i r : M.Domain} {v : Fin 26 → M.Domain} {p z : M.Domain}
      (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) (hp : M.mem p (v 11))
      (pz : Rd_entry_d p z (v 3)) : Ab_gen_d F z :=
    ⟨i,r,v 11,v 3,p,ir,⟨v,vr,rfl⟩,⟨v,vr,rfl⟩,hp,pz⟩
  have bound q (hq : Ab_gen_d F q) : M.mem q C.val := by
    obtain ⟨i,r,v,p,ir,vr,hp,pz⟩ := hq.read_l
    exact run.returned_condition_l hZF hΩ ctx ir vr hp pz
  have inhabited : ∃ p, Ab_gen_d F p := by
    obtain ⟨o,_,ho⟩ := hΩ.1.1
    obtain ⟨r,_,ir⟩ := run.function.2.1 o ho
    obtain ⟨v,vr,_⟩ := run.columns_l hZF.1 model trans ir
    have frame := (run.queues o r v ir vr).frame
    obtain ⟨p,hp⟩ := frame.generic.inhabited
    have px := frame.transitive _ frame.inside.2.2.2.2.2.1 p ((frame.accepted p).mp hp).1
    obtain ⟨z,_,pz⟩ := frame.returns.1.1.2.2 p px
    exact ⟨z,generated ir vr hp pz⟩
  have common p q (hp : Ab_gen_d F p) (hq : Ab_gen_d F q) :
      ∃ r, Ab_gen_d F r ∧ Rd_entry_d r p U.val ∧ Rd_entry_d r q U.val := by
    obtain ⟨i,r,v,a,ir,vr,ha,ap⟩ := hp.read_l
    obtain ⟨j,s,w,b,js,ws,hb,bq⟩ := hq.read_l
    have later {i r j s : M.Domain} {v w : Fin 26 → M.Domain} {a p b q : M.Domain}
        (ir : Rd_entry_d i r F) (js : Rd_entry_d j s F) (vr : Rt_tuple_d v r) (ws : Rt_tuple_d w s)
        (ha : M.mem a (v 11)) (ap : Rd_entry_d a p (v 3)) (hb : M.mem b (w 11)) (bq : Rd_entry_d b q (w 3))
        (above : i = j ∨ M.mem i j) : ∃ r, Ab_gen_d F r ∧ Rd_entry_d r p U.val ∧ Rd_entry_d r q U.val := by
      obtain ⟨a',p',ha',ap',below⟩ := run.advance_l hZF model trans hΩ ctx ir vr ha ap j s w js ws above
      have frame := (run.queues j s w js ws).frame
      obtain ⟨d,hd,da,db⟩ := (frame.filter_data_l hZF hΩ).2 a' b ha' hb
      have dx := frame.transitive _ frame.inside.2.2.2.2.2.1 d ((frame.accepted d).mp hd).1
      obtain ⟨z,_,dz⟩ := frame.returns.1.1.2.2 d dx
      have u := (ctx.rows j s w js ws).2
      have za := (frame.returns.entry_l hZF hΩ frame.transitive run.transitive frame.model run.target dz ap' u).mp da
      have zb := (frame.returns.entry_l hZF hΩ frame.transitive run.transitive frame.model run.target dz bq u).mp db
      have gen := generated js ws hd dz
      exact ⟨z,gen,ctx.order.trans _ _ _ (bound _ gen)
        (run.returned_condition_l hZF hΩ ctx js ws ha' ap')
        (run.returned_condition_l hZF hΩ ctx ir vr ha ap) za below,zb⟩
    rcases (hΩ.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i (run.function.bound_l ir).1 j (run.function.bound_l js).1 with same | lt | gt
    · exact later ir js vr ws ha ap hb bq (Or.inl (hZF.1.eq_of_same_members i j same))
    · exact later ir js vr ws ha ap hb bq (Or.inr lt)
    · obtain ⟨z,hz,zq,zp⟩ := later js ir ws vr hb bq ha ap (Or.inr gt)
      exact ⟨z,hz,zp,zq⟩
  let ρ : Env M 2 := ⟨fun k => [F,U.val].get k,fun _ => F⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (ab_gen_m (.bound 2) .newest) (rd_entry0_m .newest (.bound 1) (.bound 3))) }
  have read q : φ.denote ρ q ↔ ∃ p, Ab_gen_d F p ∧ Rd_entry_d p q U.val := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,ab_gen_sat_l hZF.1,rd_entry0_sat_l hZF.1]
    rfl
  obtain ⟨H,sep⟩ := ZF.separation_exists_d hZF φ ρ C.val
  have members q := (sep q).trans (and_congr_right fun _ => read q)
  have contained p (hp : Ab_gen_d F p) : M.mem p H := (members p).mpr ⟨bound p hp,p,hp,ctx.order.refl p (bound p hp)⟩
  refine ⟨H,members,inhabited.elim (fun p hp => ⟨p,hp,contained p hp⟩),?_,?_,?_⟩
  · intro p hp
    have pc := ((members p).mp hp).1
    exact ⟨pc,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C.val (eq ▸ pc)⟩
  · intro p q hp hq pq
    obtain ⟨pc,a,ha,ap⟩ := (members p).mp hp
    exact (members q).mpr ⟨hq,a,ha,ctx.order.trans a p q (bound a ha) pc hq ap pq⟩
  · intro p q hp hq
    obtain ⟨pc,a,ha,ap⟩ := (members p).mp hp
    obtain ⟨qc,b,hb,bq⟩ := (members q).mp hq
    obtain ⟨z,hz,za,zb⟩ := common a b ha hb
    exact ⟨z,hz,contained z hz,ctx.order.trans z a p (bound z hz) (bound a ha) pc za ap,
      ctx.order.trans z b q (bound z hz) (bound b hb) qc zb bq⟩

end YesMetaZFC.SetTheory.LargeCardinal
