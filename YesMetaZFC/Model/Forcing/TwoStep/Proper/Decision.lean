import YesMetaZFC.Model.Forcing.Proper.Hereditary.Atomic
import YesMetaZFC.Model.Forcing.Proper.Elementary.Inverse
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Density
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 二步成员判定集的内部初等闭包

每个条件或者已迫使第二坐标属于指定名称，或者以下再无这样的条件。
原子力迫在 H(χ) 中的绝对性保证这张精确判定集属于同一个 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Step_dec_d (M : SetTheory.Structure.{u}) (B R z C S F D : M.Domain) : Prop :=
  M.MemberSubset D C ∧ ∀ x, M.mem x C → (M.mem x D ↔
    Step_hits_d M B R z F x ∨ Neg_d M C S C (Step_hits_d M B R z F) x)

def step_dec_m {n} (B R z C S F D : Term n) : Formula 1 n :=
  .conj (Formula.subset D C) (Formula.forallMem C (.iff (.mem .newest D.weaken)
    (.disj (step_hits_m B.weaken R.weaken z.weaken F.weaken .newest)
      (.forallE (.imp (below_m C.weaken.weaken S.weaken.weaken C.weaken.weaken .newest (.bound 1))
        (.neg (step_hits_m B.weaken.weaken R.weaken.weaken z.weaken.weaken F.weaken.weaken .newest)))))))
derive_free_closed step_dec_m

theorem step_dec_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z C S F D : Term n) :
    Formula.satisfies ρ (step_dec_m B R z C S F D) ↔
      Step_dec_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (C.eval ρ) (S.eval ρ) (F.eval ρ) (D.eval ρ) := by
  simp only [step_dec_m, Step_dec_d, Neg_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff, step_hits_sat_l M hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, below_sat_l M hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem step_dec_exists_l (hZF : M.Models ZF) (B R z C S F : M.Domain) :
    ∃ D, Step_dec_d M B R z C S F D := by
  obtain ⟨n, φ, ρ, hφ⟩ := defined_decide_l M hZF.1 (step_hits_defined_l M hZF.1 B R z F) C S C
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ C
  exact ⟨D, fun x hx => ((hD x).mp hx).1, fun x hx => (hD x).trans ((and_iff_right hx).trans (hφ x))⟩

theorem step_dec_dense_l {B R z C S F D} (L : Cond_order_d M C S C) (hC : ¬ M.mem C C)
    (hD : Step_dec_d M B R z C S F D) : Dense_set_d M C S C D := by
  classical
  refine ⟨fun x hx => ⟨hD.1 x hx, fun he => hC (he ▸ hD.1 x hx)⟩,
    fun x hx hn => ?_⟩
  by_cases he : ∃ y, Below_d M C S C y x ∧ Step_hits_d M B R z F y
  · obtain ⟨y, hy, hh⟩ := he
    exact ⟨y, hy, (hD.2 y hy.1).mpr (Or.inl hh)⟩
  · exact ⟨x, below_refl_l L hx hn, (hD.2 x hx).mpr (Or.inr (fun y hy hh => he ⟨y, hy, hh⟩))⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H c J : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
  (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
  (hM : Smdl_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c H J)
  (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
local notation "L" => smdl_structure_l I (R := J) (And.left (And.right hM))
local notation "htr" => ZF.h_transitive_l I hZF hH
include hω hχ hωχ hH hJ

theorem smem_step_hits_l (B R z F x : (L).Domain) (hF : Name_d M B.val F.val)
    (hn : ∀ p s, KPair_d M x.val p s → Name_d M B.val s) :
    Step_hits_d L B R z F x ↔ Step_hits_d M B.val R.val z.val F.val x.val := by
  constructor
  · rintro ⟨p, s, hx, hf⟩
    have hx' := (smem_kpair_l I hM hJ htr x p s).mp hx
    exact ⟨p.val, s.val, hx', (smem_mem_force_l hZFC hω hχ hωχ hH hM hJ B R z p s F (hn _ _ hx') hF).mp hf⟩
  · rintro ⟨p, s, hx, hf⟩
    have hc := trans_kpair_l htr x.property hx
    let p' : (L).Domain := ⟨p, hc.1⟩
    let s' : (L).Domain := ⟨s, hc.2⟩
    exact ⟨p', s', (smem_kpair_l I hM hJ htr x p' s').mpr hx,
      (smem_mem_force_l hZFC hω hχ hωχ hH hM hJ B R z p' s' F (hn _ _ hx) hF).mpr hf⟩

theorem smem_step_dec_l (B R z C S F D : (L).Domain) (hF : Name_d M B.val F.val)
    (hn : ∀ x, M.mem x C.val → ∀ p s, KPair_d M x p s → Name_d M B.val s) :
    Step_dec_d L B R z C S F D ↔ Step_dec_d M B.val R.val z.val C.val S.val F.val D.val := by
  have hits (x : (L).Domain) (hx : M.mem x.val C.val) :=
    smem_step_hits_l hZFC hω hχ hωχ hH hM hJ B R z F x hF (hn _ hx)
  have neg (x : (L).Domain) : Neg_d L C S C (Step_hits_d L B R z F) x ↔
      Neg_d M C.val S.val C.val (Step_hits_d M B.val R.val z.val F.val) x.val := by
    constructor
    · intro h y hy hh
      let y' : (L).Domain := ⟨y, htr C.val C.property y hy.1⟩
      exact h y' ((smem_below_l I hM hJ htr C S C y' x).mpr hy) ((hits y' hy.1).mpr hh)
    · intro h y hy hh
      have hy' := (smem_below_l I hM hJ htr C S C y x).mp hy
      exact h y.val hy' ((hits y hy'.1).mp hh)
  constructor
  · rintro ⟨hD, hd⟩
    refine ⟨(smem_subset_l I hM hJ htr D C).mp hD, fun x hx => ?_⟩
    let x' : (L).Domain := ⟨x, htr C.val C.property x hx⟩
    exact (smem_member_l I hM hJ x' D).symm.trans
      ((hd x' ((smem_member_l I hM hJ x' C).mpr hx)).trans (or_congr (hits x' hx) (neg x')))
  · rintro ⟨hD, hd⟩
    refine ⟨(smem_subset_l I hM hJ htr D C).mpr hD, fun x hx => ?_⟩
    have hx' := (smem_member_l I hM hJ x C).mp hx
    exact (smem_member_l I hM hJ x D).trans ((hd x.val hx').trans (or_congr (hits x hx') (neg x)).symm)

omit hM in
theorem selem_step_dec_l {d N K B R z b A T W C S F}
    (hSub : Ssub_d I c d H J N K) (he : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N) (hF : M.mem F N)
    (h : Two_step_d M B R z b A T W C S) (hn : Name_d M B F) : ∃ D, M.mem D N ∧ Step_dec_d M B R z C S F D := by
  let X := smdl_structure_l I (R := J) hSub.source.2.1
  let Y := smdl_structure_l I (R := K) hSub.target.2.1
  let ρ : Env X 6 := (((((⟨fun _ => ⟨B, hSub.subset B hB⟩, fun _ => ⟨B, hSub.subset B hB⟩⟩ : Env X 1).push
    ⟨R, hSub.subset R hR⟩).push ⟨z, hSub.subset z hz⟩).push ⟨C, hSub.subset C hC⟩).push
    ⟨S, hSub.subset S hS⟩).push ⟨F, hSub.subset F hF⟩
  let η : Env Y 6 := (((((⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩ : Env Y 1).push
    ⟨R, hR⟩).push ⟨z, hz⟩).push ⟨C, hC⟩).push ⟨S, hS⟩).push ⟨F, hF⟩
  let φ : UnarySchema 6 := { body := step_dec_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ (D : X.Domain) : φ.denote ρ D ↔ Step_dec_d M B R z C S F D.val :=
    (step_dec_sat_l (smem_ext_l I hSub.source hJ htr hZF.1) _ _ _ _ _ _ _ _).trans
      (smem_step_dec_l hZFC hω hχ hωχ hH hSub.source hJ _ _ _ _ _ _ D hn
        (fun x hx p s hxp => ⟨W, ((two_step_mem_l h hxp).mp hx).1, h.closed⟩))
  obtain ⟨D, hD⟩ := step_dec_exists_l hZF B R z C S F
  have hDH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (hSub.subset C hC) D hD.1
  obtain ⟨D', hD'⟩ := selem_witness_l I hZF hω hSub he φ ρ η
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
    ⟨⟨D, hDH⟩, (hφ _).mpr hD⟩
  exact ⟨D'.val, D'.property, (hφ _).mp hD'⟩

end YesMetaZFC.Model.Forcing.Internal
