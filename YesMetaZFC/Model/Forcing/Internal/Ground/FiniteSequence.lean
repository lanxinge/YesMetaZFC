import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 成员满嵌入保持全部内部有限列

对目标模型内部 ω 上的实际公式归纳：零列来自地模型，后继列由地前缀及地末项
追加得到。因此即使内部长度外部非标准，扩张也不新增取值于地集合的有限列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

/-- 地有限列空间的规范像就是目标的全部有限列空间；不假设内部自然数标准。 -/
theorem image_fseq_l {ω X S} (hω : M.IsOmega ω) (hw : N.IsOmega (e ω))
    (hS : Fseq_space_d I ω X S) : Fseq_space_d J (e ω) (e X) (e S) := by
  let ρ : Env N 2 := (⟨fun _ => e S, fun _ => e S⟩ : Env N 1).push (e X)
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (Formula.isFunctionFromTo kpair_convention_l .newest (.bound 1) (.bound 2))
    (.mem .newest (.bound 3))) }
  have hφ n : φ.denote ρ n ↔ ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isFunctionFromTo_iff J hN.1, Formula.satisfies_mem_iff]
    rfl
  have lift : ∀ n, N.mem n (e ω) → ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S) := by
    apply hw.induction (fun n => ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S))
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hN φ ρ (e ω)
      exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
    · intro n hn f hf
      obtain ⟨a, ha, haω⟩ := hω.1.1
      have hfa : M.IsSetFunctionFromTo I a a X :=
        ⟨(Structure.IsSequenceOfLength.empty I ha).2.1,
          (Structure.IsSequenceOfLength.empty I ha).2.2, fun i hi => (ha i hi).elim⟩
      have haS := (hS a).mpr ⟨a, haω, hfa⟩
      have hEmpty : ∀ y, ¬ N.mem y f := by
        intro y hy
        obtain ⟨i, x, hp⟩ := hf.1.1 y hy
        exact hn i (hf.input_mem_of_pairMember ⟨y, hp, hy⟩)
      have hEq : e a = f := hN.1.eq_of_same_members _ _ (fun y => iff_of_false
        (fun hy => (he a y).mp hy |>.elim fun c hc => ha c hc.1) (hEmpty y))
      exact (he S f).mpr ⟨a, haS, hEq⟩
    · intro m hm ih n hn f hf
      obtain ⟨a, haω, rfl⟩ := (he ω m).mp hm
      obtain ⟨g, hg⟩ := ZF.exists_restriction hN J f (e a)
      have hgf := hg.isSetFunctionFromTo hf (fun i hi => (hn i).mpr (Or.inl hi))
      obtain ⟨s, hsS, hsg⟩ := (he S g).mp (ih g hgf)
      obtain ⟨k, hkω, hsk⟩ := (hS s).mp hsS
      have hsk' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hsk
      have hka : k = a := hi (hsk'.2.1.eq hN.1 (hsg.symm ▸ hgf.2.1))
      subst k
      obtain ⟨y, hy, hfy⟩ := hf.2.2 (e a) hn.predecessor_mem
      obtain ⟨x, hx, rfl⟩ := (he X y).mp hy
      obtain ⟨b, hb, hbω⟩ := hω.1.2 a haω
      obtain ⟨t, ht, hts⟩ := Structure.IsSequenceOfLength.exists_append (value := x)
        (ZF.modelsKP hM) I ⟨(hω.isOrdinal hM).mem haω, hsk.1, hsk.2.1⟩
        ((hω.isOrdinal hM).mem hbω) hb
      have htX : M.IsSetFunctionFromTo I t b X := by
        refine ⟨ht.2.1, ht.2.2, fun i hi => ?_⟩
        obtain ⟨v, hv⟩ := (ht.2.2 i).mp hi
        refine ⟨v, ?_, hv⟩
        rcases (hts i v).mp hv with hv | ⟨_, rfl⟩
        · exact hsk.output_mem_of_pairMember hv
        · exact hx
      have ht' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he htX
      have hEq : e t = f := by
        apply ht'.1.1.eq_of_pairMember_iff hN.1 hf.1.1
        intro i v
        change Entry_d N i v (e t) ↔ Entry_d N i v f
        rw [image_entries_l e he ht.2.1.1 i v]
        constructor
        · rintro ⟨j, w, hjw, rfl, rfl⟩
          rcases (hts j w).mp hjw with hjw | ⟨rfl, rfl⟩
          · have hv := (image_entries_l e he hsk.1.1 (e j) (e w)).mpr ⟨j, w, hjw, rfl, rfl⟩
            exact ((hg.2 (e j) (e w)).mp (hsg ▸ hv)).2
          · exact hfy
        · intro hv
          rcases (hn i).mp (hf.input_mem_of_pairMember hv) with him | him
          · have hv := hsg.symm ▸ (hg.2 i v).mpr ⟨him, hv⟩
            obtain ⟨j, w, hjw, hj, hw⟩ := (image_entries_l e he hsk.1.1 i v).mp hv
            exact ⟨j, w, (hts j w).mpr (Or.inl hjw), hj, hw⟩
          · have hei := hN.1.eq_of_same_members i (e a) him
            subst i
            exact ⟨a, x, (hts a x).mpr (Or.inr ⟨rfl, rfl⟩), rfl, hf.1.2 (e a) (e x) v hfy hv⟩
      exact (he S f).mpr ⟨t, (hS t).mpr ⟨b, hbω, htX⟩, hEq⟩
  intro f
  constructor
  · intro hf
    obtain ⟨s, hs, rfl⟩ := (he S f).mp hf
    obtain ⟨n, hn, hs⟩ := (hS s).mp hs
    exact ⟨e n, (image_member_l e hi he).mpr hn, image_function_l e hi he hs⟩
  · rintro ⟨n, hn, hf⟩
    exact lift n hn f hf

end YesMetaZFC.Model.Forcing.Internal
