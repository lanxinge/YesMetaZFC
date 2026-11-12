import YesMetaZFC.Model.Forcing.Boolean.RegularGeneric
import YesMetaZFC.Model.Forcing.Boolean.DenseExtension

/-! # 主正则开集的实际函数图

在一个正则开区域 C 上，将条件映为其主正则开集。源载体就是 C；
所有图条目及其唯一性在原模型中构造，随后用于原条件序与布尔完备化的比较。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Rpr_d (B R z p A : M.Domain) : Prop := Ropen_d B R z A ∧ M.mem p A ∧
  ∀ U, Ropen_d B R z U → M.mem p U → M.MemberSubset A U

def rpr_m {n} (B R z p A : Term n) : Formula 1 n := set[n] ⟪
  ⌜ropen_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜A⌝ₛ) ∧ ⌜p⌝ₛ ∈ ⌜A⌝ₛ ∧
  (∀ U, ⌜ropen_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,U) → ⌜p⌝ₛ ∈ U → ⌜A⌝ₛ ⊆ U)⟫
derive_free_closed rpr_m

include hZF

theorem rpr_sat_l {n} (ρ : Env M n) (B R z p A : Term n) :
    Formula.satisfies ρ (rpr_m B R z p A) ↔ Rpr_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (A.eval ρ) := by
  simp only [rpr_m,Rpr_d,Formula.satisfies_conj_iff,ropen_sat_l hZF,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  rfl

theorem Rpr_d.unique_l {B R z p A D : M.Domain} (h : Rpr_d B R z p A) (k : Rpr_d B R z p D) : A = D :=
  hZF.1.eq_of_same_members A D (fun q => ⟨h.2.2 D k.1 k.2.1 q,k.2.2 A h.1 h.2.1 q⟩)

theorem Rpr_d.dense_l {B R z p A q : M.Domain} (O : Cond_order_d M B R z)
    (h : Rpr_d B R z p A) (hq : M.mem q A) : Dense_d M B R z (fun r => Entry_d M r p R) q := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,p].get i,fun _ => B⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have read r : M.mem r D ↔ Below_d M B R z r p :=
    ((members r).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans ⟨And.right,fun hr => ⟨hr.1,hr⟩⟩
  obtain ⟨U,regular,values⟩ := ropen_closure_l hZF O D
  have hp := h.1.1 p h.2.1
  have pu := (values p).mpr ⟨hp.1,hp.2,fun r hr => ⟨r,below_refl_l O hr.1 hr.2.1,(read r).mpr hr⟩⟩
  exact fun r hr => (((values q).mp (h.2.2 U regular pu q hq)).2.2 r hr).imp fun s hs =>
    ⟨hs.1,((read s).mp hs.2).2.2⟩

omit hZF in
theorem Rpr_d.mono_l {B R z p q A D : M.Domain} (h : Rpr_d B R z p A) (k : Rpr_d B R z q D)
    (pq : Below_d M B R z p q) : M.MemberSubset A D :=
  h.2.2 D k.1 (k.1.2.1 q p (k.1.1 q k.2.1).1 pq k.2.1)

theorem rpr_graph_l {B R z C K : M.Domain} (O : Cond_order_d M B R z) (cone : Ropen_d B R z C)
    (family : ∀ A, M.mem A K ↔ Ropen_d B R z A ∧ M.MemberSubset A C) :
    ∃ F, M.IsSetFunctionFromTo I F C K ∧ ∀ p A, Entry_d M p A F ↔ M.mem p C ∧ Rpr_d B R z p A := by
  let ρ : Env M 3 := ⟨fun i => [B,R,z].get i,fun _ => B⟩
  let φ : BinarySchema 3 := { body := rpr_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat p A : φ.denote ρ p A ↔ Rpr_d B R z p A := rpr_sat_l hZF ..
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := K)
    (fun p hp => (ropen_condition_l hZF O (cone.1 p hp).1 (cone.1 p hp).2).imp fun A hA => (sat p A).mpr hA)
    (fun _ _ _ _ ha hb => ((sat _ _).mp ha).unique_l hZF ((sat _ _).mp hb))
    (fun p A hp hA => (family A).mpr ⟨((sat p A).mp hA).1,((sat p A).mp hA).2.2 C cone hp⟩)
  exact ⟨F,fn,fun p A => (graph p A).trans (and_congr_right fun _ => sat p A)⟩

end YesMetaZFC.Model.Forcing.Internal
