import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.Model.Forcing.Internal.Forcing.Definability

/-! # 主条件的加强保持与泛型意义 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem mstr_lower_l (O : Cond_order_d M B R z) {N q p}
    (hq : Mstr_d M B R z N q) (hp : Below_d M B R z p q) : Mstr_d M B R z N p :=
  ⟨hp.1, hp.2.1, fun D hD hd r hr => hq.2.2 D hD hd r (below_trans_l O hq.1 hr hp)⟩

/-- 在含全部条件的 X 上取交，不丢失稠密集中的主条件见证。 -/
theorem mstr_trace_l {N X Y q} (hX : M.MemberSubset B X)
    (hY : ∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X) (hm : Mstr_d M B R z N q) :
    Mstr_d M B R z Y q := by
  refine ⟨hm.1, hm.2.1, fun D hD hd r hr => ?_⟩
  obtain ⟨s, hsD, hsN, hc⟩ := hm.2.2 D ((hY D).mp hD).1 hd r hr
  exact ⟨s, hsD, (hY s).mpr ⟨hsN, hX s (hd.1 s hsD).1⟩, hc⟩

/-- 接受主条件的任意泛型都在 N 内遇到 N 的每个实际稠密集。 -/
theorem mstr_generic_l (hZF : M.Models ZF) {N q U}
    (hU : Generic_d M B R z U) (hq : U q) (hm : Mstr_d M B R z N q)
    {D} (hD : M.mem D N) (hd : Dense_set_d M B R z D) :
    ∃ s, M.mem s N ∧ M.mem s D ∧ U s := by
  let ρ : Env M 3 := ((⟨fun _ => D, fun _ => D⟩ : Env M 1).push N).push R
  let φ : UnarySchema 3 := {
    body := .existsE (.conj (.mem .newest (.bound 4)) (.conj (.mem .newest (.bound 3))
      (entry_m (.bound 1) .newest (.bound 2)))) }
  have hφ p : φ.denote ρ p ↔ ∃ s, M.mem s D ∧ M.mem s N ∧ Entry_d M p s R := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨p, hp, s, hsD, hsN, hps⟩ := generic_pick_l hZF hU ⟨3, φ, ρ, hφ⟩ hq (by
    intro r hr
    obtain ⟨s, hsD, hsN, p, hpr, hps⟩ := hm.2.2 D hD hd r hr
    exact ⟨p, hpr, s, hsD, hsN, hps⟩)
  exact ⟨s, hsN, hsD, hU.upward p s hp (hd.1 s hsD).1 hps⟩

end YesMetaZFC.Model.Forcing.Internal
