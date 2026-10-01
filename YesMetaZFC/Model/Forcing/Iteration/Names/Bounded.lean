import YesMetaZFC.Model.Forcing.Iteration.Names.Inclusion
import YesMetaZFC.Model.Forcing.Iteration.Stage.SystemSyntax
import YesMetaZFC.Model.Forcing.Stage.Extension
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.SetTheory.LevyReflection.Parameters

/-! # 坐标阶段包含保持原有界力迫

真实阶段泛型给出成员满嵌入，故现有 Δ₀ 公式在两侧绝对。有限参数可数反射
将此论证转成任意地模型中的力迫证书；反向由加强否定得到。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

private def Image_absolute_d {n} (φ : Formula 1 n) : Prop :=
  ∀ X Y : SetTheory.Structure.{u}, X.Models ZF → Y.Models ZF →
    ∀ e : X.Domain → Y.Domain, Function.Injective e →
      (∀ a y, Y.mem y (e a) ↔ ∃ x, X.mem x a ∧ e x = y) →
      ∀ ρ : Env X n, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l e ρ) φ

private theorem row_absolute_generic_l (hZF : M.Models ZF) {α B R D V p}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hφ : Image_absolute_d.{u} φ)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B)
    (hf : Forces_d M B R B φ ρ p) {U} (hU : Generic_d M D V D U) (hpU : U p)
    (ξ : Env (extension_l M hZF D V D U) n) (hξ : ∀ i, Qval_d M D V D U (ρ.bound i) (ξ.bound i)) :
    Formula.satisfies ξ φ := by
  obtain ⟨F, hF, hEmb⟩ := row_link_embed_l hZF k
  let G := Pull_generic_d M F U
  have hG := reg_generic_l O L hZF hEmb hU
  have hpG : G p := ⟨p, (hF p p).mpr ⟨hp, rfl⟩, hpU⟩
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have haN := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B a ha
  let σ : Env M n := ⟨ρ.bound, fun _ => a⟩
  have hσ : ∀ t : Term n, Name_d M B (t.eval σ) := by
    intro t
    cases t with
    | free _ => exact haN
    | bound i => exact hρ i
  let η := qenv_l (R := R) (z := B) (U := G) hZF σ hσ
  have hv := qenv_val_l (R := R) (z := B) (U := G) hZF σ hσ
  have hs := (forcing_truth_l O hZF hG φ hc σ η hv).mp
    ⟨p, hpG, (forces_env_l hZF.1 φ hc ρ σ (fun _ => rfl) p).mp hf⟩
  obtain ⟨e, he, hm, hi⟩ := stage_extension_l O L hZF hEmb hU
  apply (lr_env_congr_l φ hc (image_env_l e η) ξ (fun i => ?_)).mp
    ((hφ _ _ (preserves_zf_l O hZF hG) (preserves_zf_l L hZF hU) e hi hm η).mp hs)
  exact qval_unique_l (he (η.bound i) (ρ.bound i) (ρ.bound i) (hv (.bound i))
    (nmap_identity_l hZF hF (hρ i))) (hξ i)

private theorem row_absolute_push_l (hZF : M.Models ZF) {α B R D V p}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hφ : Image_absolute_d.{u} φ)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B)
    (hf : Forces_d M B R B φ ρ p) : Forces_d M D V D φ ρ p := by
  let σ : Env M (n+6) := (((((ρ.push α).push B).push R).push D).push V).push p
  let es : Fin n → Term (n+6) := fun i => .bound ⟨i.val+6, by omega⟩
  have hσ : (⟨fun i => (es i).eval σ, σ.free⟩ : Env M n) = ρ := by cases ρ; rfl
  let ψ : Formula 1 (n+6) := .conj (cond_order_m (.bound 4) (.bound 3) (.bound 4))
    (.conj (cond_order_m (.bound 2) (.bound 1) (.bound 2))
      (row_link_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1)))
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have raw (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N (n+6)) : Formula.satisfies η ψ ↔
      Cond_order_d N (η.bound 4) (η.bound 3) (η.bound 4) ∧ Cond_order_d N (η.bound 2) (η.bound 1) (η.bound 2) ∧
      Row_link_d (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN)))
        (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 2) (η.bound 1) := by
    simp only [ψ, Formula.satisfies_conj_iff, cond_order_sat_l hN.1,
      row_link_sat_l (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) hN.1]
    rfl
  obtain ⟨N, hE, hTheory, η, tr, f, hsur⟩ := FirstOrderSemantics.countable_env_l M hZF.1 σ
  have hN := (hTheory ZF).mpr hZF
  obtain ⟨O', L', k'⟩ := (raw N hN η).mp ((tr ψ hψ).mp ((raw M hZF σ).mpr ⟨O, L, k⟩))
  let ρ' : Env N n := ⟨fun i => (es i).eval η, η.free⟩
  have hn i : Name_d N (η.bound 4) (ρ'.bound i) :=
    (name_sat_l N hN.1 η (.bound 4) (es i)).mp ((tr _ (name_m_freeClosed _ _ rfl rfl)).mp
      ((name_sat_l M hZF.1 σ (.bound 4) (es i)).mpr (hρ i)))
  have hp' : N.mem (η.bound 0) (η.bound 4) := (Formula.satisfies_mem_iff η (.bound 0) (.bound 4)).mp
    ((tr (.mem (.bound 0) (.bound 4)) (by simp only [Definitional.Formula.FreeClosed]; exact ⟨rfl, rfl⟩)).mp
      ((Formula.satisfies_mem_iff σ (.bound 0) (.bound 4)).mpr hp))
  have hf' : Forces_d N (η.bound 4) (η.bound 3) (η.bound 4) φ ρ' (η.bound 0) :=
    (force_at_sat_l φ η es (.bound 4) (.bound 3) (.bound 4) (.bound 0)).mp
      ((tr _ (force_at_closed_l _ _ _ _ _ _ hc (fun _ => rfl) rfl rfl rfl rfl)).mp
        ((force_at_sat_l φ σ es (.bound 4) (.bound 3) (.bound 4) (.bound 0)).mpr (hσ.symm ▸ hf)))
  have hpD := k'.mem _ hp'
  have hg : Forces_d N (η.bound 2) (η.bound 1) (η.bound 2) φ ρ' (η.bound 0) :=
    forces_countable_l L' hN f hsur φ hc ρ' (fun i => row_name_l k' (hn i)) hpD
      (fun he => KP.mem_irrefl_d (ZF.modelsKP hN) _ (he ▸ hpD))
      (fun U hU hpU ξ hξ => row_absolute_generic_l hN O' L' k' φ hc hφ ρ' hn hp' hf' hU hpU ξ hξ)
  have hg' := (force_at_sat_l φ σ es (.bound 2) (.bound 1) (.bound 2) (.bound 0)).mp
    ((tr _ (force_at_closed_l _ _ _ _ _ _ hc (fun _ => rfl) rfl rfl rfl rfl)).mpr
      ((force_at_sat_l φ η es (.bound 2) (.bound 1) (.bound 2) (.bound 0)).mpr hg))
  exact hσ ▸ hg'

private theorem row_absolute_force_l (hZF : M.Models ZF) {α B R D V p}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hφ : Image_absolute_d.{u} φ)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B) :
    Forces_d M B R B φ ρ p ↔ Forces_d M D V D φ ρ p := by
  refine ⟨row_absolute_push_l hZF O L k φ hc hφ ρ hρ hp, fun hh => ?_⟩
  apply Classical.byContradiction
  intro hn
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hZF)
  let σ : Env M n := ⟨ρ.bound, fun _ => a⟩
  have hσ : ∀ t : Term n, Name_d M B (t.eval σ) := by
    intro t
    cases t with
    | free _ => exact name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B a ha
    | bound i => exact hρ i
  have hnσ : ¬ Forces_d M B R B φ σ p := fun hh => hn ((forces_env_l hZF.1 φ hc ρ σ (fun _ => rfl) p).mpr hh)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l O hZF φ σ hσ) hp
    (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)) hnσ
  have hnegφ : Image_absolute_d.{u} (.neg φ) := by
    intro X Y hX hY e hi he ρ
    simpa only [Formula.satisfies_neg_iff] using not_congr (hφ X Y hX hY e hi he ρ)
  have hf := row_absolute_push_l hZF O L k (.neg φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc) hnegφ σ (fun i => hσ (.bound i)) hr.1
    ((forces_neg_l hZF.1 φ σ r).mpr hneg)
  have hrD := k.mem r hr.1
  have hrd : Below_d M D V D r p := ⟨hrD, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hrD)),
    (k.order r p hr.1 hp).mpr hr.2.2⟩
  have hhσ := (forces_env_l hZF.1 φ hc ρ σ (fun _ => rfl) p).mp hh
  exact (forces_neg_l hZF.1 φ σ r).mp hf r (below_refl_l L hrD hrd.2.1)
    ((forces_regular_l L hZF φ σ (fun t => row_name_l k (hσ t))).1 p r (k.mem p hp) hrd hhσ)

/-- 原 Δ₀ 力迫在旧条件上双向对应；名称不改写，不预设泛型可延长。 -/
theorem row_delta0_force_l (hZF : M.Models ZF) {α B R D V p}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (hφ : φ.IsDelta0)
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B) :
    Forces_d M B R B φ ρ p ↔ Forces_d M D V D φ ρ p :=
  row_absolute_force_l hZF O L k φ hc
    (fun _ _ _ _ e hi he ρ => delta0_image_l e hi he hφ ρ) ρ hρ hp

/-- 旧名称关系的加强力迫直接跨阶段搬运；关系无需额外的图或函数前提。 -/
theorem row_rel_force_l (hZF : M.Models ZF) {α B R D V p T s t}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hp : M.mem p B)
    (hT : Name_d M B T) (hs : Name_d M B s) (ht : Name_d M B t) :
    Rel_force_d M B R B T p s t ↔ Rel_force_d M D V D T p s t := by
  let φ : Formula 1 3 := entry_m (.bound 1) .newest (.bound 2)
  have hf : Image_absolute_d.{u} φ := by
    intro X Y hX hY e hi he ρ
    simp only [φ, entry_sat_l X hX.1, entry_sat_l Y hY.1, eval_image_env_l]
    exact image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hX)) hY.1 _ _ _
  exact row_absolute_force_l hZF O L k φ (entry_m_freeClosed _ _ _ rfl rfl rfl) hf
    (rel_env_l M T s t) (Fin.cases ht (Fin.cases hs (fun _ => hT))) hp

end YesMetaZFC.Model.Forcing.Internal
