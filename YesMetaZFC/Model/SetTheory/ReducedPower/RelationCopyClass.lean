import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel

/-! # 实际原代表图的商类复制

类复制以两个实际类成员为见证。已有商提升的单值性保证任何源类成员
都复制到同一个目标类，不选择规范代表，也不另加几乎处处相等的前提。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Rc_class_d (X R d t Y S u π B C : M.Domain) : Prop :=
  ∃ f g, M.mem f B ∧ M.mem g C ∧ Rc_copy_d I X R d t Y S u π f g

def rc_class_m {n} (X R d t Y S u π B C : Term n) : Formula 1 n := set[n] ⟪
  ∃ f ∈ ⌜B⌝ₛ, ∃ g ∈ ⌜C⌝ₛ,
    ⌜rc_copy_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜d⌝ₛ, ⌜t⌝ₛ, ⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜u⌝ₛ, ⌜π⌝ₛ, f, g)⟫

derive_free_closed rc_class_m

theorem rc_class_sat_l (ext : Extensional M) {n} (ρ : Env M n) (X R d t Y S u π B C : Term n) :
    Formula.satisfies ρ (rc_class_m X R d t Y S u π B C) ↔
      Rc_class_d I (X.eval ρ) (R.eval ρ) (d.eval ρ) (t.eval ρ) (Y.eval ρ) (S.eval ρ)
        (u.eval ρ) (π.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [rc_class_m, Rc_class_d, Formula.satisfies_existsMem_iff, rc_copy_sat_l I ext,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, hf, g, hg, copy⟩ => ⟨f, g, hf, hg, copy⟩,
    fun ⟨f, g, hf, hg, copy⟩ => ⟨f, hf, g, hg, copy⟩⟩

/-- 实际商提升恰好读取类复制，并同时给出任意源代表的目标代表。 -/
theorem rc_copy_class_l (ext : Extensional M)
    {D E X R Y S U V F G p q C N K j d t u π : M.Domain}
    (base : FilterZF.Base_d D U) (base' : FilterZF.Base_d E V)
    (source : Rp_map_d I D X U F p C) (target : Rp_map_d I E Y V G q N)
    (fn : M.IsSetFunctionFromTo I K F G)
    (spec : ∀ f g, M.PairMember I f g K ↔ M.mem f F ∧ M.mem g G ∧ Rc_copy_d I X R d t Y S u π f g)
    (map : M.IsSetFunctionFromTo I j C N) (lift : Rp_lift_d I K p q j) :
    (∀ B A, M.PairMember I B A j ↔ M.mem B C ∧ M.mem A N ∧ Rc_class_d I X R d t Y S u π B A) ∧
    ∀ B A, M.PairMember I B A j → ∀ f, M.mem f B →
      ∃ g, M.mem g A ∧ Rc_copy_d I X R d t Y S u π f g := by
  have any B A (hBA : M.PairMember I B A j) f (hf : M.mem f B) :
      ∃ g, M.mem g A ∧ Rc_copy_d I X R d t Y S u π f g := by
    have hfp := source.member_l I ext base (map.input_mem_of_pairMember hBA) hf
    obtain ⟨g, hg, hfg⟩ := fn.2.2 f (source.projection.input_mem_of_pairMember hfp)
    obtain ⟨A', _, hgq⟩ := target.projection.2.2 g hg
    have eq := map.1.2 B A' A (lift f g B A' hfg hfp hgq) hBA
    exact ⟨g, eq ▸ target.representative_l I base' hgq, ((spec f g).mp hfg).2.2⟩
  refine ⟨fun B A => ⟨?_, ?_⟩, any⟩
  · intro hBA
    obtain ⟨f, hfp⟩ := (source.range B).mp (map.input_mem_of_pairMember hBA)
    have hf := source.representative_l I base hfp
    obtain ⟨g, hg, copy⟩ := any B A hBA f hf
    exact ⟨map.input_mem_of_pairMember hBA, map.output_mem_of_pairMember hBA, f, g, hf, hg, copy⟩
  · rintro ⟨hB, hA, f, g, hf, hg, copy⟩
    have hfp := source.member_l I ext base hB hf
    have hgq := target.member_l I ext base' hA hg
    exact lift f g B A ((spec f g).mpr ⟨source.projection.input_mem_of_pairMember hfp,
      target.projection.input_mem_of_pairMember hgq, copy⟩) hfp hgq

end YesMetaZFC.SetTheory.Internal
