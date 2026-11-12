import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Boolean.DensePush
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Return
import YesMetaZFC.Model.Forcing.Collapse.ProductTopTruth
import YesMetaZFC.Model.Forcing.Ground.FilterSet
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Collapse.ProductGroundGeneric
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.DenseEnumeration
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer

/-! # 返回映射固定整个旧前缀条件域

每行条件属于原小坍缩，整个块属于该条件域上的有限列空间。
先固定这个实际空间，再固定其前缀子集，因而同时排除目标中新出现的前缀条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_system_d.fixed_prefix_l {Ω c d X R Y S j : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (target : Smem_d I d Y S)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) (map : Smap_d I Ω c d X Y j)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B A m C T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x B)
    (fixed : Rd_entry_d s.A.val s.A.val j) (point : ∀ x, M.mem x s.A.val → Rd_entry_d x x j)
    (stage : Fp_prefix_d native ω A m C T)
    (hm : (smdl_structure_l I (R := R) source.1.2.1).mem m ω)
    (bound : ∀ i α, (smdl_structure_l I (R := R) source.1.2.1).mem i m →
      Entry_d (smdl_structure_l I (R := R) source.1.2.1) i α A →
        (smdl_structure_l I (R := R) source.1.2.1).MemberSubset α κ) :
    Rd_entry_d C.val C.val j ∧ ∀ q, M.mem q C.val → Rd_entry_d q q j := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have hw' := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eqω : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun i => ⟨hw'.2 Ω hΩ.1 i,hΩ.2 ω.val hw'.1 i⟩)
  obtain ⟨fixedQ,pointQ,_⟩ := s.fixed_small_l hZF hΩ source target xt yt map native inh fixed point
  obtain ⟨W,space⟩ := ZF.fseq_space_exists_l J native hw p.Q
  have space' := image_fseq_l native hZF Subtype.val inj full hw hw' space
  have space' : Fseq_space_d I Ω p.Q.val W.val := eqω ▸ space'
  obtain ⟨fixedW,pointW⟩ := map.fixed_fseq_l hZF hΩ xt yt source target
    (eqω ▸ ω.property) fixedQ pointQ W.property space'
  have sub : M.MemberSubset C.val W.val := by
    intro q hq
    obtain ⟨q₀,hq₀,rfl⟩ := (full C q).mp hq
    have fq := (stage.conditions q₀).mp hq₀
    apply member.mpr
    refine (space q₀).mpr ⟨m,hm,fq.function,fq.domain,?_⟩
    intro i hi
    obtain ⟨t,it⟩ := (fq.domain i).mp hi
    obtain ⟨α,k,iα,hk,ft⟩ := fq.coordinates i t it
    refine ⟨t,(p.small_space t).mpr ⟨k,hk,ft.1,ft.2.1,?_⟩,it⟩
    intro a ha
    obtain ⟨x,hx,ax⟩ := ft.2.2 a ha
    exact ⟨x,bound i α hi iα x hx,ax⟩
  exact ⟨map.fixed_subset_l hZF hΩ xt yt source target fixedW pointW C.property sub,
    fun q hq => pointW q (sub q hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 返回枝上同一滤子列的前缀泛型性

原小泛型沿专用返回枝提升。运输稠密比较图后正向恢复前缀滤子，
整个旧条件域的固定性把它识别为原背景滤子列，并给出同一小扩张与前缀扩张的同构。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.prefix_generic_l {Ω c X R z Q G b f F K : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B A m C T a Γ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x B)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (stage : Fp_prefix_d native ω A m C T)
    (hm : (smdl_structure_l I (R := R) source.1.2.1).mem m ω)
    (bound : ∀ i α, (smdl_structure_l I (R := R) source.1.2.1).mem i m →
      Entry_d (smdl_structure_l I (R := R) source.1.2.1) i α A →
        (smdl_structure_l I (R := R) source.1.2.1).MemberSubset α κ)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) C T C
      (fun q => (smdl_structure_l I (R := R) source.1.2.1).mem q C ∧ Fp_ready_d I m.val F q.val))
    (ha : (smdl_structure_l I (R := R) source.1.2.1).mem a C ∧ Fp_ready_d I m.val F a.val)
    (map : Dmap_at_d p.Q p.T p.Q C T C Γ a) (sub : M.MemberSubset K p.Q.val)
    (read : ∀ q : (smdl_structure_l I (R := R) source.1.2.1).Domain,
      M.mem q.val K ↔ Pull_generic_d (smdl_structure_l I (R := R) source.1.2.1) Γ
        (fun t => (smdl_structure_l I (R := R) source.1.2.1).mem t C ∧ Fp_ready_d I m.val F t.val) q) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ x, Rd_entry_d x.val (e x).val r.j) ∧
      (e ω).val = Ω ∧ (e m).val = m.val ∧
      Fp_prefix_d r.native (e ω) (e A) (e m) (e C) (e T) ∧
      let H := fun q : N'.Domain => N'.mem q (e C) ∧ Fp_ready_d I (e m).val F q.val
      Generic_d N' (e C) (e T) (e C) H ∧
      Generic_d N' (e p.Q) (e p.T) (e p.Q) (fun q => M.mem q.val K) ∧
      Miso_over_d (extension_l N' r.native (e p.Q) (e p.T) (e p.Q) (fun q => M.mem q.val K))
        (extension_l N' r.native (e C) (e T) (e C) H)
        (Gval_d N' (e p.Q) (e p.T) (e p.Q) (fun q => M.mem q.val K)) (Gval_d N' (e C) (e T) (e C) H) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let H := fun q : N.Domain => N.mem q C ∧ Fp_ready_d I m.val F q.val
  let V := fun q : N.Domain => M.mem q.val K
  have same : Pull_generic_d N Γ H = V := funext fun q => propext (read q).symm
  have small : Generic_d N p.Q p.T p.Q V := same ▸ reg_generic_l p.small_order (stage.order_l native) native
    map.toReg_map_d generic (map.toReg_map_d.dense_hit_l native (stage.order_l native) generic ha map.dense)
  obtain ⟨e,elem,values,small',_,_⟩ := s.small_generic_l hZF hΩ source r.target xt r.transitive r.map
    native r.native inh r.fixed r.point small
  have fixedC := s.fixed_prefix_l hZF hΩ source r.target xt r.transitive r.map native hw inh r.fixed r.point stage hm bound
  obtain ⟨fixedQ,pointQ,_⟩ := s.fixed_small_l hZF hΩ source r.target xt r.transitive r.map native inh r.fixed r.point
  have point (U : N.Domain) (pt : ∀ x, M.mem x U.val → Rd_entry_d x x r.j) (x : N.Domain) (hx : N.mem x U) :
      (e x).val = x.val := r.map.1.1.1.2 _ _ _ (values x) (pt x.val ((source.2 x.val U.val).mp hx).2.2)
  have covers (U : N.Domain) (fixed : Rd_entry_d U.val U.val r.j)
      (pt : ∀ x, M.mem x U.val → Rd_entry_d x x r.j) (q : N'.Domain) (hq : N'.mem q (e U)) :
      ∃ x, N.mem x U ∧ e x = q := by
    have eq := r.map.1.1.1.2 _ _ _ (values U) fixed
    have hq' : M.mem q.val U.val := eq ▸ ((r.target.2 q.val (e U).val).mp hq).2.2
    let x : N.Domain := ⟨q.val,xt U.val U.property q.val hq'⟩
    have hx : N.mem x U := (source.2 x.val U.val).mpr ⟨x.property,U.property,hq'⟩
    exact ⟨x,hx,Subtype.ext (point U pt x hx)⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have hw' := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eqω : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun i => ⟨hw'.2 Ω hΩ.1 i,hΩ.2 ω.val hw'.1 i⟩)
  have mn := r.map.natural_l hZF hΩ xt r.transitive source r.target (eqω ▸ ω.property) m.val
    (eqω ▸ ((source.2 m.val ω.val).mp hm).2.2)
  have em : (e m).val = m.val := r.map.1.1.1.2 _ _ _ (values m) mn
  have ew : (e ω).val = Ω := (r.map.1.1.1.2 _ _ _ (values ω) (r.images 0)).trans r.omega
  let H' := fun q : N'.Domain => N'.mem q (e C) ∧ Fp_ready_d I (e m).val F q.val
  have movedH : Em_generic_d e H = H' := by
    funext q
    apply propext
    constructor
    · rintro ⟨t,⟨ht,ready⟩,rfl⟩
      exact ⟨(em_member_l e elem t C).mp ht,by simpa only [em,point C fixedC.2 t ht] using ready⟩
    · rintro ⟨hq,ready⟩
      obtain ⟨t,ht,rfl⟩ := covers C fixedC.1 fixedC.2 q hq
      exact ⟨t,⟨ht,by simpa only [em,point C fixedC.2 t ht] using ready⟩,rfl⟩
  have movedK : Em_generic_d e V = (fun q : N'.Domain => M.mem q.val K) := by
    funext q
    apply propext
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact (point p.Q pointQ t (small.proper t ht).1).symm ▸ ht
    · intro hq
      let t : N.Domain := ⟨q.val,xt p.Q.val p.Q.property q.val (sub q.val hq)⟩
      have ht : N.mem t p.Q := (source.2 t.val p.Q.val).mpr ⟨t.property,p.Q.property,sub q.val hq⟩
      exact ⟨t,hq,Subtype.ext (point p.Q pointQ t ht)⟩
  have stage' := fp_prefix_image_l native r.native e elem stage
  have map' := map.image_l native.1 r.native.1 e elem
  have recovery : Push_generic_d C T Γ V = H := by
    rw [← same]
    exact map.push_pull_l native (stage.order_l native) generic ha
  have pushed := map'.push_generic_l r.native (stage'.order_l r.native) ((em_member_l e elem a C).mp ha.1) small'
  have pushEq : Push_generic_d (e C) (e T) (e Γ) (Em_generic_d e V) = H' :=
    (map.push_image_l native.1 r.native.1 e elem small.proper (covers C fixedC.1 fixedC.2)).trans
      ((congrArg (Em_generic_d e) recovery).trans movedH)
  have generic' : Generic_d N' (e C) (e T) (e C) H' := pushEq ▸ pushed
  have pullEq : Pull_generic_d N' (e Γ) H' = (fun q => M.mem q.val K) := by
    rw [← movedH,map.pull_image_l native.1 r.native.1 e elem H (covers p.Q fixedQ pointQ),same,movedK]
  have accepted : H' (e a) := movedH ▸ (show Em_generic_d e H (e a) from ⟨a,ha,rfl⟩)
  have iso := map'.toReg_map_d.dense_ground_l r.native
    (em_order_l native.1 r.native.1 e elem p.small_order) (stage'.order_l r.native)
    map'.functional generic' accepted map'.dense
  exact ⟨e,elem,values,ew,em,stage',generic',movedK ▸ small',pullEq ▸ iso⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 8.5 吸收后继的有限条件兑现

7.23 的同一返回模型及小泛型保持固定。在其小扩张内对大坍缩作有限值交换，
使新大泛型接受任意给定条件；滤子由原交换图在背景中分离成实际集合，
扩张同构把已吸收实数的完整图搬到同一集合所生成的新扩张。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 由原专用系统自动读取分支中的有限坍缩，而不另交目标空间证书。 -/
theorem Ag_branch_d.collapse_data_l {Ω c X R z Q G b f : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    (∃ ℓ, Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) ℓ (r.w 3)) ∧
      ∀ q t, Entry_d N q t (r.w 4) ↔ N.mem q (r.w 3) ∧ N.mem t (r.w 3) ∧ N.MemberSubset t q := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let φ : Formula 1 3 := set[3] ⟪
    (∃ ℓ, ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜(.bound 0 : Term 3)⌝ₛ,ℓ,⌜(.bound 1 : Term 3)⌝ₛ)) ∧
    (∀ q t, ⌜entry_m⌝ₚ(q,t,⌜(.bound 2 : Term 3)⌝ₛ) ↔
      q ∈ ⌜(.bound 1 : Term 3)⌝ₛ ∧ t ∈ ⌜(.bound 1 : Term 3)⌝ₛ ∧ t ⊆ q)⟫
  let ρ : Env N 3 := ⟨fun i => [ω,p.P,p.U].get i,fun _ => ω⟩
  let η : Env N' 3 := ⟨fun i => [r.w 0,r.w 3,r.w 4].get i,fun _ => r.w 0⟩
  have truth : Formula.satisfies ρ φ := by
    simp only [φ,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,
      fseq_space_sat_l (kp_pair_l (ZF.modelsKP native)) native.1,
      Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l N native.1,
      Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
    exact ⟨⟨δ,p.big_space⟩,p.big_edges⟩
  have moved := (smap_source_l I hZF hw source.1 r.target.1 r.map φ
    (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) ρ η
    (Fin.cases (r.images 0) (Fin.cases (r.images 3) (Fin.cases (r.images 4) (fun i => Fin.elim0 i))))).mp truth
  simp only [φ,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,
    fseq_space_sat_l (kp_pair_l (ZF.modelsKP r.native)) r.native.1,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l N' r.native.1,
    Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken] at moved
  exact moved

/-- 固定小扩张后，任意有限大条件都可与指定实数的吸收同时实现。 -/
def Ag_condition_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H x : M.Domain) : Prop :=
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  ∃ e : N.Domain → E.Domain, Function.Injective e ∧
    (∀ a y, E.mem y (e a) ↔ ∃ q, N.mem q a ∧ e q = y) ∧
    (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
    ∃ hE : E.Models ZF, ∀ p, E.mem p (e (r.w 3)) →
      ∃ K : M.Domain, M.MemberSubset K (r.w 3).val ∧
      Generic_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun q => M.mem q.val K)) ∧
      Em_generic_d e (fun q => M.mem q.val K) p ∧
      let D := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun q => M.mem q.val K))
      ∃ j : N.Domain → D.Domain, Function.Injective j ∧
        (∀ a, Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3))
          (Em_generic_d e (fun q => M.mem q.val K)) (e a) (j a)) ∧
        ∃ A y, Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
          ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x)

theorem Ag_real_d.condition_l {Ω c X R z Q G b f H x : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (real : Ag_real_d hZF r H x)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
      (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)) : Ag_condition_d hZF r H x := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  obtain ⟨e,ei,ef,checks,_,t,K,_,big,prod,τ,A',_,_,j,ji,_,jchecks,y,_,_,_,_,_,
    hE,u,um,ui,uo,over,fn,read,unique⟩ := real
  obtain ⟨O,_,_,_⟩ := r.small_data_l hZF hw source native s
  obtain ⟨L,_⟩ := r.dense_data_l hZF hw source native s
  obtain ⟨_,OP,hb,top,_⟩ := r.product_data_l hZF hw source native s
  obtain ⟨⟨ℓ,space⟩,edges⟩ := r.collapse_data_l hZF hw source native s
  have ord := image_cond_order_l (ZF.modelsKP r.native) hE.1 e ei ef L
  have omega := image_omega_l (hEN := hE.1) e ei ef r.native
    (internal_foundation_l O r.native small) r.frame.omega
    (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e (r.w 0)))
  let G₀ := Em_generic_d e (fun q : N.Domain => M.mem q.val K)
  let D₀ := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) G₀
  have hD₀ : D₀.Models ZF := preserves_zf_l ord hE big
  obtain ⟨q,hq⟩ := prod.inhabited
  have base := prod.upward q (r.w 8) hq hb (top q (prod.proper q hq).1)
  have ground a : Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) G₀ (e a) (u (j a)) := by
    obtain ⟨w,check,_,_⟩ := zf_check_l N r.native hb a
    exact (over a (j a)).mp ⟨r.w 8,w,base,check,jchecks a w check⟩
  refine ⟨e,ei,ef,checks,hE,?_⟩
  intro p hp
  obtain ⟨p₀,hp₀,eqp⟩ := (ef (r.w 3) p).mp hp
  obtain ⟨F,aut,result⟩ := fseq_ground_retarget_l r.native hE e ei ef r.frame.omega omega space L edges big hp₀
  obtain ⟨K₁,sub,members⟩ := r.target.filter_pull_set_l hZF r.transitive (r.w 3) (r.w 4) F aut K
  have predicates : Pull_generic_d N F (fun q => M.mem q.val K) = (fun q => M.mem q.val K₁) :=
    funext fun q => propext (members q).symm
  rw [predicates] at result
  obtain ⟨gen,accepted,v,vm,vi,vo,vg⟩ := result
  let G₁ := Em_generic_d e (fun q : N.Domain => M.mem q.val K₁)
  let D₁ := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) G₁
  have hD₁ : D₁.Models ZF := preserves_zf_l ord hE gen
  have iso : Miso_over_d D₁ D₀ (Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) G₁)
      (Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) G₀) := ⟨v,vm,vi,vo,vg⟩
  obtain ⟨w,wm,wi,wo,wg⟩ := iso.symm_l
  have wf (a : D₀.Domain) (b : D₁.Domain) : D₁.mem b (w a) ↔ ∃ c, D₀.mem c a ∧ w c = b := by
    obtain ⟨c,hc⟩ := wo b
    constructor
    · intro h
      refine ⟨c,(wm c a).mpr ?_,hc⟩
      rw [hc]
      exact h
    · rintro ⟨d,hd,eq⟩
      rw [← eq]
      exact (wm d a).mp hd
  have transported g : Fn_read_d Subtype.val (w ∘ u ∘ j) (w (u y)) g ↔
      Fn_read_d Subtype.val (u ∘ j) (u y) g := by
    apply forall_congr' fun i => forall_congr' fun a => iff_congr Iff.rfl ?_
    apply exists_congr fun k => exists_congr fun b => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact (image_entry_iff_l w wi wf (KP.exists_pair (ZF.modelsKP hD₀)) hD₁.1 (u (j k)) (u (j b)) (u y)).symm
  have fn' := image_function_l (hEN := hD₁.1) (hPN := KP.exists_pair (ZF.modelsKP hD₁))
    w wi wf (fn0_function_l (ZF.modelsKP hD₀) fn)
  exact ⟨K₁,sub,gen,⟨p₀,accepted,eqp⟩,w ∘ u ∘ j,wi.comp (ui.comp ji),
    fun a => (wg (e a) (u (j a))).mp (ground a),A',w (u y),
    fn0_of_function_l (ZF.modelsKP hD₁) fn',(transported x).mpr read,
    fun g hg => (transported g).trans (unique g hg)⟩

/-- 同一实际返回枝承担有限条件任务；根复合式及原临界点下界完整保留。 -/
theorem Ag_return_d.condition_l {Ω c X R z d Y π f H x : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (returned : Ag_return_d hZF Ω z c X d Y π (fun i => (s.aux_params_l native i).val) f H x) :
    ∃ ρ γ T Q G E b, Rk_d I (s.aux_params_l native 10).val ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
      It_tree_d hZF Ω c Ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
      It_return_at_d hZF Ω z T Q G d Y π b ∧ It_wf_branch_d hZF Ω Ω T Q G b ∧
      ∃ r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f, ∃ σ,
        Smap_d I Ω r.d d r.N Y σ ∧ It_comp_d r.j σ π ∧
        M.CardinalLessOrEqual I r.N Ω ∧
        Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
          (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) ∧
        Ag_real_d hZF r H x ∧ Ag_condition_d hZF r H x := by
  obtain ⟨ρ,γ,T,Q,G,E,b,rk,low,ordinal,tree,bound,branch,wf,r,σ,map,square,count,small,real⟩ := returned
  exact ⟨ρ,γ,T,Q,G,E,b,rk,low,ordinal,tree,bound,branch,wf,r,σ,map,square,
    count,small,real,real.condition_l hZF hw source native s small⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 吸收得到的实际滤子写入全乘积任务列

下一坐标的条件由待完成的全乘积条件读取。有限改写生产背景滤子 K，
随后将 K 追加到同一序列，冻结旧坐标并推进任务进度；实数解释留在该 K 的实际扩张中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已写入状态的背景滤子及其实际扩张中的同一实数。 -/
def Ag_filter_d {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (H x K : M.Domain) : Prop :=
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  M.MemberSubset K (r.w 3).val ∧
  ∃ e : N.Domain → E.Domain, Function.Injective e ∧
    (∀ a y, E.mem y (e a) ↔ ∃ q, N.mem q a ∧ e q = y) ∧
    (∀ a t, Check_d N (r.w 7) a t → Qval_d N (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) t (e a)) ∧
    ∃ hE : E.Models ZF,
      Generic_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun q => M.mem q.val K)) ∧
      let D := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun q => M.mem q.val K))
      ∃ j : N.Domain → D.Domain, Function.Injective j ∧
        (∀ a, Gval_d E (e (r.w 3)) (e (r.w 4)) (e (r.w 3))
          (Em_generic_d e (fun q => M.mem q.val K)) (e a) (j a)) ∧
        ∃ A y, Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
          ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x)

/-- 指定下一坐标的条件后，生产实际新滤子和新前缀，不要求调用者提供推进公理。 -/
theorem Ag_condition_d.append_l {Ω z c X Q G b f H x n F d : M.Domain} {v : Fin 19 → M.Domain}
    {r : Ag_branch_d hZF Ω z c X Q G b v f} (h : Ag_condition_d hZF r H x)
    (hw : M.IsOmega Ω) (hn : M.mem n Ω) (seq : M.IsSequenceOfLength I F n)
    (fd : M.IsSetFunction I d) (ready : Fp_ready_d I n F d)
    (p : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (hp : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem p (r.w 3))
    (next : Entry_d M n p.val d) :
    ∃ m F' K, M.SuccessorOf m n ∧ M.mem m Ω ∧ M.IsSequenceOfLength I F' m ∧
      M.IsRestrictionOf I F F' n ∧ Entry_d M n K F' ∧
      Fp_ready_d I m F' d ∧ M.mem p.val K ∧ Ag_filter_d hZF r H x K := by
  obtain ⟨e,ei,ef,checks,hE,conditions⟩ := h
  obtain ⟨K,sub,generic,accepted,j,ji,ground,A,y,fn,read,unique⟩ :=
    conditions (e p) ((image_member_l e ei ef).mpr hp)
  obtain ⟨q,hq,eq⟩ := accepted
  have accepted : M.mem p.val K := congrArg Subtype.val (ei eq) ▸ hq
  obtain ⟨m,F',succ,hm,seq',cut,last,ready'⟩ := fp_ready_append_l I hZF hw hn seq fd ready next accepted
  exact ⟨m,F',K,succ,hm,seq',cut,last,ready',accepted,
    sub,e,ei,ef,checks,hE,generic,j,ji,ground,A,y,fn,read,unique⟩

/-- 继续兑现已保存的同一条件块；终点 m 和条件 d 不作重新选择。 -/
theorem Ag_condition_d.continue_l {Ω z c X Q G b f H x F : M.Domain} {v : Fin 19 → M.Domain}
    {r : Ag_branch_d hZF Ω z c X Q G b v f} (h : Ag_condition_d hZF r H x) (hw : M.IsOmega Ω)
    (A n m d κ : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunction (kp_pair_l (ZF.modelsKP r.native)) A)
    (hn : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n (r.w 0))
    (hm : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem m (r.w 0))
    (lt : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n m)
    (fd : Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) A m d)
    (alphabet : Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) n κ A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) κ (r.w 3))
    (seq : M.IsSequenceOfLength I F n.val) (ready : Fp_ready_d I n.val F d.val) :
    ∃ n' F' K, M.SuccessorOf n' n.val ∧ M.mem n' Ω ∧ M.MemberSubset n' m.val ∧
      M.IsSequenceOfLength I F' n' ∧ M.IsRestrictionOf I F F' n.val ∧ Entry_d M n.val K F' ∧
      Fp_ready_d I n' F' d.val ∧ Ag_filter_d hZF r H x K := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let J := kp_pair_l (ZF.modelsKP r.native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have hn' : M.mem n.val Ω := by simpa only [r.omega] using (show M.mem n.val (r.w 0).val from member.mpr hn)
  obtain ⟨p,np⟩ := (fd.domain n).mp lt
  obtain ⟨κ',k,nκ,hk,fp⟩ := fd.coordinates n p np
  have eq := fa.2 n κ' κ nκ alphabet
  subst κ'
  have hp := (space p).mpr ⟨k,hk,fp⟩
  obtain ⟨U,range⟩ := ZF.exists_range_of_setFunction r.native J fd.function fd.domain
  have fn : N.IsSetFunctionFromTo J d m U := ⟨fd.function,fd.domain,fun i hi => by
    obtain ⟨p,ip⟩ := (fd.domain i).mp hi
    exact ⟨p,(range p).mpr ⟨i,ip⟩,ip⟩⟩
  have ff := image_function_l (M := N) (N := M) (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full fn
  have point := (image_entry_iff_l Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1 n p d).mp np
  obtain ⟨n',F',K,succ,hn',seq',keep,last,ready',_,filter⟩ := h.append_l hZF hw hn' seq ff.1 ready p hp point
  have sub : M.MemberSubset n.val m.val := (image_subset_iff_l Subtype.val inj full).mpr
    ((r.frame.omega.members_areOrdinals (ZF.modelsKP r.native) m hm).transitive n lt)
  refine ⟨n',F',K,succ,hn',?_,seq',keep,last,ready',filter⟩
  intro i hi
  rcases (succ i).mp hi with hi | eq
  · exact sub i hi
  · exact (hZF.1.eq_of_same_members i n.val eq).symm ▸ member.mpr lt

/-- 选择覆盖下一坐标的实际全乘积任务，并立即兑现其第一项。 -/
theorem Ag_condition_d.task_l {Ω z c X Q G b f H x F : M.Domain} {v : Fin 19 → M.Domain}
    {r : Ag_branch_d hZF Ω z c X Q G b v f} (h : Ag_condition_d hZF r H x) (hw : M.IsOmega Ω)
    (A P R C S D n κ : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunction (kp_pair_l (ZF.modelsKP r.native)) A)
    (product : Fp_product_d r.native (r.w 0) A P R)
    (hn : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n (r.w 0))
    (stage : Fp_prefix_d r.native (r.w 0) A n C S)
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) C S C
      (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
    (dense : Dense_set_d (smdl_structure_l I (R := r.W) r.target.1.2.1) P R P D)
    (alphabet : Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) n κ A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) κ (r.w 3))
    (seq : M.IsSequenceOfLength I F n.val) :
    ∃ m d : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain,
      M.mem m.val Ω ∧ M.mem n.val m.val ∧
      (smdl_structure_l I (R := r.W) r.target.1.2.1).mem d D ∧
      Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) A m d ∧
      Fp_ready_d I n.val F d.val ∧
      ∃ n' F' K, M.SuccessorOf n' n.val ∧ M.mem n' Ω ∧ M.MemberSubset n' m.val ∧
        M.IsSequenceOfLength I F' n' ∧ M.IsRestrictionOf I F F' n.val ∧ Entry_d M n.val K F' ∧
        Fp_ready_d I n' F' d.val ∧ Ag_filter_d hZF r H x K := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP r.native)) hZF.1
  obtain ⟨m,d,q,hm,lt,dD,fd,cut,_,ready⟩ := product.task_l r.native r.frame.omega hn alphabet stage generic dense
  have hm' : M.mem m.val Ω := by simpa only [r.omega] using (show M.mem m.val (r.w 0).val from member.mpr hm)
  have ready' : Fp_ready_d I n.val F d.val := by
    intro i p hi ambient
    obtain ⟨i₀,p₀,edge₀,ei,ep⟩ := (image_entries_l (M := N) (N := M) Subtype.val full fd.function.1 i p).mp ambient
    have hi₀ : M.mem i₀.val n.val := ei.symm ▸ hi
    obtain ⟨K,iK,pK⟩ := ready i₀.val p₀.val hi₀
      ((entry i₀ p₀ q).mp ((cut.2 i₀ p₀).mpr ⟨member.mp hi₀,edge₀⟩))
    exact ⟨K,ei ▸ iK,ep ▸ pK⟩
  exact ⟨m,d,hm',member.mpr lt,dD,fd,ready',h.continue_l hZF hw A n m d κ fa hn hm lt fd alphabet space seq ready'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一吸收滤子的前缀拼接及实数保持

把已吸收的大泛型沿小扩张与前缀扩张的同构运输，追加同一个背景滤子 K。
新前缀扩张与原吸收扩张同构，指定实数的全部图边随之保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_filter_d.prefix_step_l {Ω c X R z Q G b f H x K F F' : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (filter : Ag_filter_d hZF r H x K)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
      (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    {A n m C S D V ℓ W : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain}
    (stage : Fp_prefix_d r.native (r.w 0) A n C S) (next : Fp_prefix_d r.native (r.w 0) A m D V)
    (hn : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n (r.w 0))
    (hm : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem m (r.w 0))
    (succ : (smdl_structure_l I (R := r.W) r.target.1.2.1).SuccessorOf m n)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP r.native)) A (r.w 0) W)
    (alphabet : Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) n ℓ A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) ℓ (r.w 3))
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) C S C
      (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
    (comparison : Miso_over_d
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native
        (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native C S C
        (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
      (Gval_d _ (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (Gval_d _ C S C (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val)))
    (ff : M.IsSetFunction I F') (keep : M.IsRestrictionOf I F F' n.val) (last : Entry_d M n.val K F') :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ Z, M.MemberSubset Z D.val ∧
      (∀ t, M.mem t Z ↔ M.mem t D.val ∧ Fp_ready_d I m.val F' t) ∧
      Generic_d N D V D (fun q => M.mem q.val Z) ∧
      Gset_d D.val V.val D.val r.N Z ∧
      let E := extension_l N r.native D V D (fun q => M.mem q.val Z)
      ∃ j : N.Domain → E.Domain, Function.Injective j ∧
        (∀ a, Gval_d N D V D (fun q => M.mem q.val Z) a (j a)) ∧
        ∃ A y, Fn_bg_d r.N D.val V.val D.val (r.w 0).val A.val Z x ∧
          Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
          ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x) := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H)
  obtain ⟨O,hb,top,_⟩ := r.small_data_l hZF hΩ source native s
  obtain ⟨L,_⟩ := r.dense_data_l hZF hΩ source native s
  obtain ⟨_,edges⟩ := r.collapse_data_l hZF hΩ source native s
  obtain ⟨_,e,ei,ef,checks,hE,big,j,ji,ground,A₀,y,fn,read,unique⟩ := filter
  obtain ⟨q,hq⟩ := small.inhabited
  have accepted := small.upward q (r.w 7) hq hb (top q (small.proper q hq).1)
  -- 同一背景 K 在前缀扩张上仍泛型，第二步同构保持分支模型的全部地值。
  obtain ⟨a,ha,k,ki,kf,kc,big',stepIso⟩ := comparison.check_step_l r.native O (stage.order_l r.native) L
    small generic accepted e ei ef checks big
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  obtain ⟨Z,sub,members,newGeneric,newIso⟩ := fp_ground_successor_l r.native hZF Subtype.val inj full
    stage next r.frame.omega hn hm succ fa alphabet space L edges generic ha k ki kf kc big' ff keep last
  let Old := extension_l E hE (e (r.w 3)) (e (r.w 4)) (e (r.w 3)) (Em_generic_d e (fun q : N.Domain => M.mem q.val K))
  let New := extension_l N r.native D V D (fun q : N.Domain => M.mem q.val Z)
  have oldZF : Old.Models ZF := preserves_zf_l (image_cond_order_l (ZF.modelsKP r.native) hE.1 e ei ef L) hE big
  have newZF : New.Models ZF := preserves_zf_l (next.order_l r.native) r.native newGeneric
  have genericCode := (r.target.generic_code_l I hZF.1 r.transitive (ZF.modelsKP r.native) D V D Z).mpr ⟨sub,newGeneric⟩
  -- 新前缀、前缀二步扩张和原吸收扩张形成同一交换链。
  have iso := newIso.trans_l stepIso.symm_l
  obtain ⟨v,vm,vi,vo,vg⟩ := iso.symm_l
  have vf a b : New.mem b (v a) ↔ ∃ c, Old.mem c a ∧ v c = b := by
    obtain ⟨c,rfl⟩ := vo b
    exact ⟨fun h => ⟨c,(vm c a).mpr h,rfl⟩,fun ⟨d,hd,eq⟩ => eq ▸ (vm d a).mp hd⟩
  have transported g : Fn_read_d Subtype.val (v ∘ j) (v y) g ↔ Fn_read_d Subtype.val j y g := by
    apply forall_congr' fun i => forall_congr' fun a => iff_congr Iff.rfl ?_
    apply exists_congr fun k => exists_congr fun b => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact (image_entry_iff_l v vi vf (KP.exists_pair (ZF.modelsKP oldZF)) newZF.1 (j k) (j b) y).symm
  have fn' := image_function_l (hEN := newZF.1) (hPN := KP.exists_pair (ZF.modelsKP newZF))
    v vi vf (fn0_function_l (ZF.modelsKP oldZF) fn)
  have ground' a := (vg a (j a)).mp (ground a)
  have function := fn0_of_function_l (ZF.modelsKP newZF) fn'
  have read' := (transported x).mpr read
  have code := fn_code_of_value_l r.native (next.order_l r.native) newGeneric Subtype.val (v ∘ j) ground' function read'
  have background := (fn_bg_read_l I hZF.1 r.target r.transitive r.native.1 D V D (r.w 0) A₀ Z x).mpr code
  exact ⟨Z,sub,members,newGeneric,genericCode,v ∘ j,vi.comp ji,ground',
    A₀,v y,background,function,read',
    fun g hg => (transported g).trans (unique g hg)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 返回阶段的全乘积和全部出生任务的背景编号

返回构造已证明该同一模型在背景中可数。任意实际字母表列据此产生
全乘积、其全部稠密集族以及覆盖整个任务族的背景 ω 枚举。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.task_family_l {Ω z c X Q G b f : M.Domain} {v : Fin 19 → M.Domain}
    (r : Ag_branch_d hZF Ω z c X Q G b v f) (count : M.CardinalLessOrEqual I r.N Ω)
    (A U : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP r.native)) A (r.w 0) U) :
    ∃ P R D : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain,
      Fp_product_d r.native (r.w 0) A P R ∧
      (∀ E, (smdl_structure_l I (R := r.W) r.target.1.2.1).mem E D ↔
        Dense_set_d (smdl_structure_l I (R := r.W) r.target.1.2.1) P R P E) ∧
      ∃ e, M.IsSetFunctionFromTo I e Ω D.val ∧ M.IsSetSurjectiveOnto I e Ω D.val := by
  obtain ⟨P,R,product⟩ := fp_product_l r.native r.frame.omega fa
  obtain ⟨D,family,e,fn,onto⟩ := r.target.dense_enumeration_l hZF r.transitive r.native count
    P R (product.order_l r.native)
  exact ⟨P,R,D,product,family,e,fn,onto⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 待完成稠密任务沿同一返回嵌入搬运

整块条件和原稠密集沿实际根腿运输；内部自然数终点固定。
已冻结坐标的字母表包含于原小坍缩字母表时，其条件属于已证明逐点固定的小条件域，
所以原背景滤子列仍接受搬运后的同一前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.task_move_l {Ω c X R z Q G b f F : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (inh : ∃ x, (smdl_structure_l I (R := R) source.1.2.1).mem x B)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (e : (smdl_structure_l I (R := R) source.1.2.1).Domain →
      (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (elem : Pe_d e) (values : ∀ x, Rd_entry_d x.val (e x).val r.j)
    (A P T D n m d : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (product : Fp_product_d native ω A P T)
    (dense : Dense_set_d (smdl_structure_l I (R := R) source.1.2.1) P T P D)
    (hit : (smdl_structure_l I (R := R) source.1.2.1).mem d D)
    (hn : (smdl_structure_l I (R := R) source.1.2.1).mem n ω)
    (hm : (smdl_structure_l I (R := R) source.1.2.1).mem m ω)
    (fd : Fp_at_d (kp_pair_l (ZF.modelsKP native)) ω A m d)
    (sub : (smdl_structure_l I (R := R) source.1.2.1).MemberSubset n m)
    (bound : ∀ i α, (smdl_structure_l I (R := R) source.1.2.1).mem i n →
      Entry_d (smdl_structure_l I (R := R) source.1.2.1) i α A →
        (smdl_structure_l I (R := R) source.1.2.1).MemberSubset α κ)
    (ready : Fp_ready_d I n.val F d.val) :
    (e ω).val = Ω ∧ (e n).val = n.val ∧ (e m).val = m.val ∧
      Fp_product_d r.native (e ω) (e A) (e P) (e T) ∧
      Dense_set_d (smdl_structure_l I (R := r.W) r.target.1.2.1) (e P) (e T) (e P) (e D) ∧
      (smdl_structure_l I (R := r.W) r.target.1.2.1).mem (e d) (e D) ∧
      Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (e ω) (e A) (e m) (e d) ∧
      Fp_ready_d I n.val F (e d).val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have inj' : Function.Injective (Subtype.val : N'.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full' := smem_full_l I r.target r.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have hw' := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eqω : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun i => ⟨hw'.2 Ω hΩ.1 i,hΩ.2 ω.val hw'.1 i⟩)
  have omega_mem : M.mem Ω X := eqω ▸ ω.property
  have natural := r.map.natural_l hZF hΩ xt r.transitive source r.target omega_mem
  have fixed {i : N.Domain} (hi : N.mem i ω) : (e i).val = i.val :=
    r.map.1.1.1.2 i.val (e i).val i.val (values i) (natural i.val (eqω ▸ member.mpr hi))
  have omega_image : (e ω).val = Ω := r.map.1.1.1.2 Ω (e ω).val Ω
    (eqω ▸ values ω) (r.map.omega_l I hZF hΩ xt r.transitive source r.target omega_mem)
  obtain ⟨_,smallFixed,_⟩ := s.fixed_small_l hZF hΩ source r.target xt r.transitive r.map native inh r.fixed r.point
  have moved := fp_at_image_l native r.native e elem fd
  obtain ⟨V,range⟩ := ZF.exists_range_of_setFunction r.native (kp_pair_l (ZF.modelsKP r.native)) moved.function moved.domain
  have fn' : N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP r.native)) (e d) (e m) V :=
    ⟨moved.function,moved.domain,fun i hi => by
      obtain ⟨a,ia⟩ := (moved.domain i).mp hi
      exact ⟨a,(range a).mpr ⟨i,ia⟩,ia⟩⟩
  have fn := (image_function_l (M := N') (N := M) (hEN := hZF.1)
    (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj' full' fn').1
  have row_fixed {i q : N.Domain} (hi : N.mem i n) (iq : Entry_d N i q d) : (e q).val = q.val := by
    obtain ⟨α,k,iα,hk,fq⟩ := fd.coordinates i q iq
    have fq' : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) q k κ :=
      ⟨fq.1,fq.2.1,fun j hj => by
        obtain ⟨a,ha,ja⟩ := fq.2.2 j hj
        exact ⟨a,bound i α hi iα a ha,ja⟩⟩
    have hq := (p.small_space q).mpr ⟨k,hk,fq'⟩
    exact r.map.1.1.1.2 q.val (e q).val q.val (values q) (smallFixed q.val (member.mpr hq))
  refine ⟨omega_image,fixed hn,fixed hm,fp_product_image_l native r.native e elem product,
    fp_dense_image_l e elem native.1 r.native.1 dense,(em_member_l e elem d D).mp hit,moved,?_⟩
  intro i q hi iq
  let i₀ : N.Domain := ⟨i,xt n.val n.property i hi⟩
  have hi₀ : N.mem i₀ n := member.mp hi
  obtain ⟨a,ia⟩ := (fd.domain i₀).mp (sub i₀ hi₀)
  have ei : (e i₀).val = i := fixed (hw.transitive (ZF.modelsKP native) n hn i₀ hi₀)
  have ea := row_fixed hi₀ ia
  have targetEntry := (em_entry_l native.1 r.native.1 e elem i₀ a d).mp ia
  have targetEntry' : Entry_d M i a.val (e d).val := by
    have ent := (image_entry_iff_l (M := N') (N := M) Subtype.val inj' full'
      (KP.exists_pair (ZF.modelsKP r.native)) hZF.1 (e i₀) (e a) (e d)).mp targetEntry
    simpa only [ei,ea] using ent
  have sourceEntry := (image_entry_iff_l (M := N) (N := M) Subtype.val inj full
    (KP.exists_pair (ZF.modelsKP native)) hZF.1 i₀ a d).mp ia
  have eq := fn.2 i a.val q targetEntry' iq
  obtain ⟨K,iK,aK⟩ := ready i a.val hi sourceEntry
  exact ⟨K,iK,eq ▸ aK⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全乘积稠密任务的泛型后继出口

从原稠密集实际选择任务；未完成时追加吸收所得滤子，自动构造下一前缀，
同时返回严格进度、整个新前缀的泛型性及指定实数在该扩张中的图解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 待完成任务的后续回合：始终兑现给定 d，保持给定有限终点 m。 -/
theorem Ag_condition_d.continue_successor_l {Ω c X R z Q G b f H x F : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (h : Ag_condition_d hZF r H x)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
      (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (A P T C S n m d ℓ W : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP r.native)) A (r.w 0) W)
    (product : Fp_product_d r.native (r.w 0) A P T)
    (hn : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n (r.w 0))
    (hm : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem m (r.w 0))
    (lt : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n m)
    (fd : Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) A m d)
    (stage : Fp_prefix_d r.native (r.w 0) A n C S)
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) C S C
      (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
    (comparison : Miso_over_d
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native
        (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native C S C
        (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
      (Gval_d _ (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (Gval_d _ C S C (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val)))
    (alphabet : Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) n ℓ A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) ℓ (r.w 3))
    (seq : M.IsSequenceOfLength I F n.val) (ready : Fp_ready_d I n.val F d.val) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ n' C' S' : N.Domain, ∃ F' K Z : M.Domain,
      N.SuccessorOf n' n ∧ N.mem n' (r.w 0) ∧ M.MemberSubset n'.val m.val ∧
      M.IsSequenceOfLength I F' n'.val ∧ M.IsRestrictionOf I F F' n.val ∧ Entry_d M n.val K F' ∧
      Fp_ready_d I n'.val F' d.val ∧ Ag_filter_d hZF r H x K ∧
      Fp_prefix_d r.native (r.w 0) A n' C' S' ∧ M.MemberSubset Z C'.val ∧
      (∀ t, M.mem t Z ↔ M.mem t C'.val ∧ Fp_ready_d I n'.val F' t) ∧
      Generic_d N C' S' C' (fun q => M.mem q.val Z) ∧
      Gset_d C'.val S'.val C'.val r.N Z ∧
      let E := extension_l N r.native C' S' C' (fun q => M.mem q.val Z)
      ∃ j : N.Domain → E.Domain, Function.Injective j ∧
        (∀ a, Gval_d N C' S' C' (fun q => M.mem q.val Z) a (j a)) ∧
        ∃ A y, Fn_bg_d r.N C'.val S'.val C'.val (r.w 0).val A.val Z x ∧
          Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
          ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x) := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨n₁,F',K,succ₁,_,bound,seq',keep,last,ready',filter⟩ :=
    h.continue_l hZF hΩ A n m d ℓ fa.1 hn hm lt fd alphabet space seq ready
  obtain ⟨n',succ,hn'⟩ := r.frame.omega.1.2 n hn
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have moved := image_successor_l (hEN := hZF.1) Subtype.val inj full r.native.1 succ
  have eq : n₁ = n'.val := succ₁.eq hZF.1 moved
  subst n₁
  obtain ⟨C',S',next⟩ := product.prefix_l r.native hn'
  obtain ⟨Z,subZ,members,newGeneric,genericCode,real⟩ := filter.prefix_step_l hZF hΩ source native s small
    stage next hn hn' succ fa alphabet space generic comparison seq'.2.1 keep last
  exact ⟨n',C',S',F',K,Z,succ,hn',bound,seq',keep,last,ready',filter,next,subZ,members,newGeneric,genericCode,real⟩

theorem Ag_condition_d.task_successor_l {Ω c X R z Q G b f H x F : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (h : Ag_condition_d hZF r H x)
    (small : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
      (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
    (A P T C S D n ℓ W : (smdl_structure_l I (R := r.W) r.target.1.2.1).Domain)
    (fa : (smdl_structure_l I (R := r.W) r.target.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP r.native)) A (r.w 0) W)
    (product : Fp_product_d r.native (r.w 0) A P T)
    (hn : (smdl_structure_l I (R := r.W) r.target.1.2.1).mem n (r.w 0))
    (stage : Fp_prefix_d r.native (r.w 0) A n C S)
    (generic : Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1) C S C
      (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
    (comparison : Miso_over_d
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native
        (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (extension_l (smdl_structure_l I (R := r.W) r.target.1.2.1) r.native C S C
        (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
      (Gval_d _ (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H))
      (Gval_d _ C S C (fun q => (smdl_structure_l I (R := r.W) r.target.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val)))
    (dense : Dense_set_d (smdl_structure_l I (R := r.W) r.target.1.2.1) P T P D)
    (alphabet : Entry_d (smdl_structure_l I (R := r.W) r.target.1.2.1) n ℓ A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) ℓ (r.w 3))
    (seq : M.IsSequenceOfLength I F n.val) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ m d : N.Domain, M.mem m.val Ω ∧ M.mem n.val m.val ∧ N.mem d D ∧
      Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) A m d ∧ Fp_ready_d I n.val F d.val ∧
      ∃ n' C' S' : N.Domain, ∃ F' K Z : M.Domain,
        N.SuccessorOf n' n ∧ N.mem n' (r.w 0) ∧ M.MemberSubset n'.val m.val ∧
        M.IsSequenceOfLength I F' n'.val ∧ M.IsRestrictionOf I F F' n.val ∧ Entry_d M n.val K F' ∧
        Fp_ready_d I n'.val F' d.val ∧ Ag_filter_d hZF r H x K ∧
        Fp_prefix_d r.native (r.w 0) A n' C' S' ∧ M.MemberSubset Z C'.val ∧
        (∀ t, M.mem t Z ↔ M.mem t C'.val ∧ Fp_ready_d I n'.val F' t) ∧
        Generic_d N C' S' C' (fun q => M.mem q.val Z) ∧
        Gset_d C'.val S'.val C'.val r.N Z ∧
        let E := extension_l N r.native C' S' C' (fun q => M.mem q.val Z)
        ∃ j : N.Domain → E.Domain, Function.Injective j ∧
          (∀ a, Gval_d N C' S' C' (fun q => M.mem q.val Z) a (j a)) ∧
          ∃ A y, Fn_bg_d r.N C'.val S'.val C'.val (r.w 0).val A.val Z x ∧
            Fn0_d (j (r.w 0)) (j A) y ∧ Fn_read_d Subtype.val j y x ∧
            ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x) := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨m,d,hm,lt,dD,fd,ready,n₁,F',K,succ₁,_,bound,seq',keep,last,ready',filter⟩ :=
    h.task_l hZF hΩ A P T C S D n ℓ fa.1 product hn stage generic dense alphabet space seq
  obtain ⟨n',succ,hn'⟩ := r.frame.omega.1.2 n hn
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I r.target r.transitive
  have moved := image_successor_l (hEN := hZF.1) Subtype.val inj full r.native.1 succ
  have eq : n₁ = n'.val := succ₁.eq hZF.1 moved
  subst n₁
  obtain ⟨C',S',next⟩ := product.prefix_l r.native hn'
  obtain ⟨Z,subZ,members,newGeneric,genericCode,real⟩ := filter.prefix_step_l hZF hΩ source native s small
    stage next hn hn' succ fa alphabet space generic comparison seq'.2.1 keep last
  exact ⟨m,d,hm,lt,dD,fd,ready,n',C',S',F',K,Z,succ,hn',bound,seq',keep,last,ready',filter,next,subZ,members,newGeneric,genericCode,real⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一待完成任务跨实际返回枝推进

返回因子、内部 ZFC、可数性、全乘积和原稠密任务一同运输。
前缀比较及任务运输使用同一根映射；随后兑现原条件的下一坐标，保留原有限终点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_return_d.pending_l {Ω c X R z cY Y π f H x F : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (xt : M.TransitiveSet X) (certificate : Zc_model_d I Ω c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ B A P U C S D n m d W a Γ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ B} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (inh : ∃ y, (smdl_structure_l I (R := R) source.1.2.1).mem y B)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W)
    (product : Fp_product_d native ω A P U) (stage : Fp_prefix_d native ω A n C S)
    (hn : (smdl_structure_l I (R := R) source.1.2.1).mem n ω)
    (hm : (smdl_structure_l I (R := R) source.1.2.1).mem m ω)
    (lt : (smdl_structure_l I (R := R) source.1.2.1).mem n m)
    (fd : Fp_at_d (kp_pair_l (ZF.modelsKP native)) ω A m d)
    (dense : Dense_set_d (smdl_structure_l I (R := R) source.1.2.1) P U P D)
    (hit : (smdl_structure_l I (R := R) source.1.2.1).mem d D)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) n δ A)
    (bound : ∀ i α, (smdl_structure_l I (R := R) source.1.2.1).mem i n →
      Entry_d (smdl_structure_l I (R := R) source.1.2.1) i α A →
        (smdl_structure_l I (R := R) source.1.2.1).MemberSubset α κ)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) C S C
      (fun q => (smdl_structure_l I (R := R) source.1.2.1).mem q C ∧ Fp_ready_d I n.val F q.val))
    (ha : (smdl_structure_l I (R := R) source.1.2.1).mem a C ∧ Fp_ready_d I n.val F a.val)
    (map : Dmap_at_d p.Q p.T p.Q C S C Γ a) (subH : M.MemberSubset H p.Q.val)
    (read : ∀ q : (smdl_structure_l I (R := R) source.1.2.1).Domain,
      M.mem q.val H ↔ Pull_generic_d (smdl_structure_l I (R := R) source.1.2.1) Γ
        (fun t => (smdl_structure_l I (R := R) source.1.2.1).mem t C ∧ Fp_ready_d I n.val F t.val) q)
    (seq : M.IsSequenceOfLength I F n.val) (ready : Fp_ready_d I n.val F d.val)
    (returned : Ag_return_d hZF Ω z c X cY Y π (fun i => (s.aux_params_l native i).val) f H x) :
    ∃ ρ γ T₀ Q₀ G₀ E₀ b, Rk_d I (s.aux_params_l native 10).val ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
      It_tree_d hZF Ω c Ω T₀ Q₀ G₀ E₀ ∧ It_critical_bound_d I γ Q₀ E₀ ∧
      It_return_at_d hZF Ω z T₀ Q₀ G₀ cY Y π b ∧ It_wf_branch_d hZF Ω Ω T₀ Q₀ G₀ b ∧
      ∃ r : Ag_branch_d hZF Ω z c X Q₀ G₀ b (fun i => (s.aux_params_l native i).val) f, ∃ σ,
        Smap_d I Ω r.d cY r.N Y σ ∧ It_comp_d r.j σ π ∧ M.CardinalLessOrEqual I r.N Ω ∧
        Zc_model_d I Ω r.d r.N r.W ∧
        let N := smdl_structure_l I (R := R) source.1.2.1
        let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
        ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ y, Rd_entry_d y.val (e y).val r.j) ∧
          (e n).val = n.val ∧ (e m).val = m.val ∧
          Fp_product_d r.native (r.w 0) (e A) (e P) (e U) ∧
          Dense_set_d N' (e P) (e U) (e P) (e D) ∧ N'.mem (e d) (e D) ∧
          Fp_at_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) (e A) (e m) (e d) ∧
          ∃ n' C' S' : N'.Domain, ∃ F' K Z : M.Domain,
            N'.SuccessorOf n' (e n) ∧ N'.mem n' (r.w 0) ∧ M.MemberSubset n'.val m.val ∧
            M.IsSequenceOfLength I F' n'.val ∧ M.IsRestrictionOf I F F' n.val ∧ Entry_d M n.val K F' ∧
            Fp_ready_d I n'.val F' (e d).val ∧ Ag_filter_d hZF r H x K ∧
            Fp_prefix_d r.native (r.w 0) (e A) n' C' S' ∧ M.MemberSubset Z C'.val ∧
            (∀ t, M.mem t Z ↔ M.mem t C'.val ∧ Fp_ready_d I n'.val F' t) ∧
            Generic_d N' C' S' C' (fun q => M.mem q.val Z) ∧
            Gset_d C'.val S'.val C'.val r.N Z ∧
            (n' = e m → M.mem (e d).val Z) ∧
            let E := extension_l N' r.native C' S' C' (fun q => M.mem q.val Z)
            ∃ j : N'.Domain → E.Domain, Function.Injective j ∧
              (∀ y, Gval_d N' C' S' C' (fun q => M.mem q.val Z) y (j y)) ∧
              ∃ A' y, Fn_bg_d r.N C'.val S'.val C'.val (r.w 0).val A'.val Z x ∧
                Fn0_d (j (r.w 0)) (j A') y ∧ Fn_read_d Subtype.val j y x ∧
                ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val j y g ↔ g = x) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  obtain ⟨ρ,γ,T₀,Q₀,G₀,E₀,b,rk,low,ordinal,tree,critical,branch,wf,r,σ,returnMap,square,count,small,_,condition⟩ :=
    returned.condition_l hZF hΩ source native s
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨e,elem,values,_,en,stage',generic',_,comparison⟩ :=
    r.prefix_generic_l hZF hΩ source xt native s hw inh stage hn bound generic ha map subH read
  have params i : e (s.aux_params_l native i) = r.w i :=
    Subtype.ext (r.map.1.1.1.2 _ _ _ (values (s.aux_params_l native i)) (r.images i))
  have ew : e ω = r.w 0 := params 0
  have eqQ : e p.Q = r.w 1 := params 1
  have eqT : e p.T = r.w 2 := params 2
  have eqP : e p.P = r.w 3 := params 3
  rw [eqQ,eqT] at comparison
  rw [ew] at stage'
  have sub := (hw.members_areOrdinals (ZF.modelsKP native) m hm).transitive n lt
  obtain ⟨_,_,em,product',dense',hit',fd',ready'⟩ :=
    r.task_move_l hZF hΩ source xt native s hw inh e elem values A P U D n m d product dense hit hn hm fd sub bound ready
  rw [ew] at product' fd'
  have hn' : N'.mem (e n) (r.w 0) := ew ▸ (em_member_l e elem n ω).mp hn
  have hm' : N'.mem (e m) (r.w 0) := ew ▸ (em_member_l e elem m ω).mp hm
  have lt' := (em_member_l e elem n m).mp lt
  have fa' : N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP r.native)) (e A) (r.w 0) (e W) := by
    let η : Env N 3 := ⟨fun i => [A,ω,W].get i,fun _ => A⟩
    let φ := Formula.isFunctionFromTo kpair_convention_l (.bound 0 : Term 3) (.bound 1) (.bound 2)
    have moved := (elem φ (by simp -implicitDefEqProofs [φ]) η).mp
      ((Formula.satisfies_isFunctionFromTo_iff (kp_pair_l (ZF.modelsKP native)) native.1 η _ _ _).mpr fa)
    exact ew ▸ (Formula.satisfies_isFunctionFromTo_iff (kp_pair_l (ZF.modelsKP r.native)) r.native.1 (image_env_l e η) _ _ _).mp moved
  have space : Fseq_space_d (kp_pair_l (ZF.modelsKP r.native)) (r.w 0) (e δ) (r.w 3) := by
    let η : Env N 3 := ⟨fun i => [ω,δ,p.P].get i,fun _ => ω⟩
    let φ := fseq_space_m (𝒞 := kpair_convention_l) (.bound 0 : Term 3) (.bound 1) (.bound 2)
    have moved := (elem φ (by simp -implicitDefEqProofs [φ]) η).mp
      ((fseq_space_sat_l (kp_pair_l (ZF.modelsKP native)) native.1 η _ _ _).mpr p.big_space)
    exact ew ▸ eqP ▸ (fseq_space_sat_l (kp_pair_l (ZF.modelsKP r.native)) r.native.1 (image_env_l e η) _ _ _).mp moved
  have alphabet' := (em_entry_l native.1 r.native.1 e elem n δ A).mp alphabet
  obtain ⟨n',C',S',F',K,Z,succ,hn'',bound',seq',keep,last,ready'',filter,next,subZ,members,newGeneric,genericCode,real⟩ :=
    condition.continue_successor_l hZF hΩ source native s small (e A) (e P) (e U) (e C) (e S) (e n) (e m) (e d) (e δ) (e W)
      fa' product' hn' hm' lt' fd' stage' generic' comparison alphabet' space (en.symm ▸ seq) (en.symm ▸ ready')
  have done (eq : n' = e m) : M.mem (e d).val Z := by
    have hd := (next.conditions (e d)).mpr (eq.symm ▸ fd')
    exact (members (e d).val).mpr ⟨((r.target.2 (e d).val C'.val).mp hd).2.2,ready''⟩
  exact ⟨ρ,γ,T₀,Q₀,G₀,E₀,b,rk,low,ordinal,tree,critical,branch,wf,r,σ,returnMap,square,count,
    certificate.map_l hZF hΩ r.target.1 r.map,e,elem,values,en,em,product',dense',hit',fd',
    n',C',S',F',K,Z,succ,hn'',em ▸ bound',seq',en ▸ keep,en ▸ last,ready'',filter,next,subZ,members,newGeneric,genericCode,done,real⟩

end YesMetaZFC.SetTheory.LargeCardinal
