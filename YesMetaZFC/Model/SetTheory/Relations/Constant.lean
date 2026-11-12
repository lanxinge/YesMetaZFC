import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.Extensionality
import YesMetaZFC.Model.SetTheory.Relations.SeparationSource

/-! # 原关系中的实际常值与恒等函数

常值图就是结构内部的乘积 D × {x}，无需传递性、分离或选择。
恒等图在原结构的 D × D 中直接分离，不借用另一个字面模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_constant_raw_l (ext : Extensional M) (ρ : Env M 0)
    (algebra : Formula.satisfies ρ sc_algebra_m) (d x : M.Domain) :
    ∃ B f, Fn0_d d B f ∧ ∀ s, M.mem s d → Rd_entry_d s x f := by
  obtain ⟨B, hB⟩ := algebra.1.1 x x
  have singleton := (pair0_sat_l ext (((ρ.push x).push x).push B) .newest (.bound 2) (.bound 1)).mp hB
  have bx : M.mem x B := (singleton x).mpr (Or.inl rfl)
  have unique y (hy : M.mem y B) : y = x := ((singleton y).mp hy).elim id id
  obtain ⟨f, hf⟩ := algebra.1.2.2.1 d B
  change Formula.satisfies (((ρ.push d).push B).push f) (ri_image_m .prod (.bound 2) (.bound 1) .newest) at hf
  simp only [ri_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, ri_value_sat_l ext, ri_guard_sat_l ext,
    Definitional.Term.eval_weaken] at hf
  change (∀ p, M.mem p f → ∃ s, M.mem s d ∧ ∃ y, M.mem y B ∧ KPair_d M p s y) ∧
    (∀ s, M.mem s d → ∀ y, M.mem y B → True → ∃ p, M.mem p f ∧ KPair_d M p s y) at hf
  have value s (hs : M.mem s d) : Rd_entry_d s x f := by
    obtain ⟨p, hp, code⟩ := hf.2 s hs x bx trivial
    exact ⟨p, code, hp⟩
  exact ⟨B, f, ⟨hf.1, fun s hs => ⟨x, bx, value s hs⟩,
    fun _ _ y hy z hz _ _ => (unique y hy).trans (unique z hz).symm⟩, value⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原关系分离在已有乘积中产生同一结构的恒等图。 -/
theorem sc_identity_raw_l {ω c Y S : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c Y S) (theory : Sc_theory_d I ω Y S)
    (en : Extensional (smdl_structure_l I (R := S) model.2.1))
    (d : (smdl_structure_l I (R := S) model.2.1).Domain) :
    ∃ f : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d d d f ∧
      ∀ x, Rd_entry_d x.val d.val S → Rd_entry_d x x f := by
  let N := smdl_structure_l I (R := S) model.2.1
  let ρ : Env N 0 := ⟨Fin.elim0, fun _ => d⟩
  obtain ⟨P, prod⟩ := (theory.algebra model.2.1 ρ).1.2.2.1 d d
  change Formula.satisfies (((ρ.push d).push d).push P) (ri_image_m .prod (.bound 2) (.bound 1) .newest) at prod
  simp only [ri_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, ri_value_sat_l en, ri_guard_sat_l en,
    Definitional.Term.eval_weaken] at prod
  change (∀ p, N.mem p P → ∃ x, N.mem x d ∧ ∃ y, N.mem y d ∧ KPair_d N p x y) ∧
    (∀ x, N.mem x d → ∀ y, N.mem y d → True → ∃ p, N.mem p P ∧ KPair_d N p x y) at prod
  let φ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (kpair0_m (.bound 1) .newest .newest) }
  let η : Env N 1 := ⟨fun _ => d, fun _ => d⟩
  have read p : φ.denote η p ↔ ∃ x, N.mem x d ∧ KPair_d N p x x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l en]; rfl
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c) hω
  obtain ⟨f, hf, sep⟩ := sc_separate_raw_l I hZF hω model theory model identity φ η P
  let F : N.Domain := ⟨f, hf⟩
  have members p : N.mem p F ↔ ∃ x, N.mem x d ∧ KPair_d N p x x := by
    refine ⟨fun hp => (read p).mp ((sep p).mp hp).2, fun ⟨x, hx, pair⟩ => ?_⟩
    obtain ⟨v, hv, pv⟩ := prod.2 x hx x hx trivial
    exact (sep p).mpr ⟨kpair_unique_l N en pv pair ▸ hv, (read p).mpr ⟨x, hx, pair⟩⟩
  have graph x y : Rd_entry_d x y F ↔ N.mem x d ∧ x = y := by
    constructor
    · rintro ⟨p, pair, hp⟩
      obtain ⟨v, hv, pv⟩ := (members p).mp hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l N pair pv
      exact ⟨hv, rfl⟩
    · rintro ⟨hx, rfl⟩
      obtain ⟨p, _, pair⟩ := prod.2 x hx x hx trivial
      exact ⟨p, pair, (members p).mpr ⟨x, hx, pair⟩⟩
  refine ⟨F, ⟨?_, fun x hx => ⟨x, hx, (graph x x).mpr ⟨hx, rfl⟩⟩, ?_⟩,
    fun x hx => (graph x x).mpr ⟨hx, rfl⟩⟩
  · intro p hp
    obtain ⟨x, hx, pair⟩ := (members p).mp hp
    exact ⟨x, hx, x, hx, pair⟩
  · exact fun x _ y _ z _ hxy hxz => ((graph x y).mp hxy).2.symm.trans ((graph x z).mp hxz).2

end YesMetaZFC.SetTheory.Internal
