import YesMetaZFC.Model.SetTheory.Internal.SourceBranchSyntax
import YesMetaZFC.Model.SetTheory.Internal.SourceAlgebra

/-! # 枝反射与统一标签关系的良基性

每条标签关系的下降都保持原载体和原关系。枝反射排除这样的下降；反向则
给任何外部下降枝逐点加标签，用统一关系的良基性迫使源内已经存在枝。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem sb_bad_wf_l {ω X Q : M.Domain} (hDC : Dc_d I ω) (branches : Sc_branch_d ω X)
    (rel : ∀ u v, M.mem u X → M.mem v X → (Rd_entry_d u v Q ↔ Sb_bad_d ω X u v)) : Wf_rel_d X Q := by
  intro B sub ⟨u, hu⟩
  apply Classical.byContradiction
  intro no
  have prev v (hv : M.mem v B) : ∃ w, M.mem w B ∧ Rd_entry_d w v Q := by
    apply Classical.byContradiction
    intro nh
    exact no ⟨v, hv, fun w hw hr => nh ⟨w, hw, hr⟩⟩
  obtain ⟨v, hv, hvu⟩ := prev u hu
  obtain ⟨A, R, hA, hR, ⟨x, _, y, hy, _, hty, _⟩, absent⟩ := (rel v u (sub v hv) (sub u hu)).mp hvu
  have wf : Wf_rel_d A R := wf_of_no_desc_l hZF hDC
    (fun f hf hd => absent (branches A R hA hR ⟨f, hf, hd⟩))
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (rd_triple0_m .newest (.bound 3) (.bound 4) (.bound 1)) }
  let ρ : Env M 3 := ⟨Fin.cases B (Fin.cases A (fun _ => R)), fun _ => B⟩
  obtain ⟨C, spec⟩ := ZF.separation_exists_d hZF φ ρ A
  have cs z : M.mem z C ↔ M.mem z A ∧ ∃ w, M.mem w B ∧ Rd_triple_d w A R z := by
    simpa only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_triple0_sat_l hZF.1] using! spec z
  obtain ⟨z, hz, least⟩ := wf C (fun z hz => ((cs z).mp hz).1) ⟨y, (cs y).mpr ⟨hy, u, hu, hty⟩⟩
  obtain ⟨_, w, hw, htw⟩ := (cs z).mp hz
  obtain ⟨v, hv, hvw⟩ := prev w hw
  obtain ⟨A', R', _, _, ⟨x', hx', y', _, htx, hty', hr⟩, _⟩ := (rel v w (sub v hv) (sub w hw)).mp hvw
  obtain ⟨ea, er, ey⟩ := pc_triple_inj_l hty' htw
  subst A' R' y'
  exact least x' ((cs x').mpr ⟨hx', v, hv, htx⟩) hr

theorem sb_bad_branch_l {ω X Q : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (algebra : Sc_algebra_d X) (wf : Wf_rel_d X Q)
    (rel : ∀ u v, M.mem u X → M.mem v X → (Rd_entry_d u v Q ↔ Sb_bad_d ω X u v)) : Sc_branch_d ω X := by
  intro A R hA hR ⟨f, hf, hd⟩
  apply Classical.byContradiction
  intro absent
  have tag x (hx : M.mem x A) : ∃ u, M.mem u X ∧ Rd_triple_d u A R x := by
    obtain ⟨v, hv, hc⟩ := algebra.kpair_l hR (hX A hA x hx)
    obtain ⟨u, hu, he⟩ := algebra.kpair_l hA hv
    exact ⟨u, hu, v, hc, he⟩
  let φ : BinarySchema 3 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (rd_triple0_m (.bound 1) (.bound 4) (.bound 5) .newest)) }
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases A (fun _ => R)), fun _ => f⟩
  have val i u : φ.denote ρ i u ↔ ∃ x, Rd_entry_d i x f ∧ Rd_triple_d u A R x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rd_triple0_sat_l hZF.1]; rfl
  obtain ⟨g, hg, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i hi => by
      obtain ⟨x, hx, hix⟩ := hf.2.1 i hi
      obtain ⟨u, _, hu⟩ := tag x hx
      exact ⟨u, (val i u).mpr ⟨x, hix, hu⟩⟩)
    (fun i _ u v hu hv => by
      obtain ⟨x, hix, hx⟩ := (val i u).mp hu
      obtain ⟨y, hiy, hy⟩ := (val i v).mp hv
      have eq := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 i y x hiy hix
      exact pn_triple_unique_l hZF.1 hx (eq ▸ hy))
    (fun i u _ hu => by
      obtain ⟨x, hix, hx⟩ := (val i u).mp hu
      obtain ⟨v, hv, ht⟩ := tag x (hf.bound_l hix).2
      exact pn_triple_unique_l hZF.1 ht hx ▸ hv)
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) hg)
  intro i m u v hmi hiu hmv
  obtain ⟨x, hix, htx⟩ := (val i u).mp ((gs i u).mp hiu).2
  obtain ⟨y, hmy, hty⟩ := (val m v).mp ((gs m v).mp hmv).2
  exact (rel v u (hg.output_mem_of_pairMember hmv) (hg.output_mem_of_pairMember hiu)).mpr
    ⟨A, R, hA, hR, ⟨y, (hf.bound_l hmy).2, x, (hf.bound_l hix).2, hty, htx, hd i m x y hmi hix hmy⟩, absent⟩

end YesMetaZFC.SetTheory.Internal
