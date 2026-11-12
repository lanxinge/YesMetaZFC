import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 最大集合的实际内部指令

在 V(η+1) 中，Vη 是按包含关系最大的元素。用七条原指令表达
∀A∀x(x∈A→x∈v_b)，从而在限制公式中绑定前一秩层，无须把它加作类型常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_top_d (Y X : M.Domain) : Prop := M.mem X Y ∧ ∀ a, M.mem a Y → M.MemberSubset a X

theorem Sr_top_d.unique_l (hE : Extensional M) {Y X Z : M.Domain} (h : Sr_top_d Y X) (k : Sr_top_d Y Z) : X = Z :=
  hE.eq_of_same_members X Z (fun x => ⟨k.2 X h.1 x, h.2 Z k.1 x⟩)

theorem sr_top_power_l {X Y : M.Domain} (h : M.IsPowerSetOf Y X) : Sr_top_d Y X :=
  ⟨(h X).mpr (fun _ h => h), fun a ha => (h a).mp ha⟩

def Sr_top_code_d (b G w : M.Domain) : Prop := ∃ i j a d e t u v,
  M.SuccessorOf i b ∧ M.SuccessorOf j i ∧ Sr_at_d I 0 G a j i ∧ Sr_at_d I 0 G d j b ∧
    Sr_at_d I 2 G e a a ∧ Sr_at_d I 2 G t e d ∧ Sr_at_d I 3 G u j t ∧
      Sr_at_d I 3 G v i u ∧ Sr_at_d I 2 G w v v

def sr_top_code_m {d} (b G w : Term d) : Formula 1 d := set[d] ⟪
  ∃ i j a d e t u v, ⌜Formula.isSuccessor⌝ₚ(i, ⌜b⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(j, i) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, a, j, i) ∧ ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, d, j, ⌜b⌝ₛ) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, e, a, a) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, t, e, d) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, u, j, t) ∧ ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, v, i, u) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜w⌝ₛ, v, v)⟫
derive_free_closed sr_top_code_m

theorem sr_top_code_sat_l {d} (ρ : Env M d) (b G w : Term d) :
    Formula.satisfies ρ (sr_top_code_m (𝒞 := 𝒞) b G w) ↔ Sr_top_code_d I (b.eval ρ) (G.eval ρ) (w.eval ρ) := by
  simp only [sr_top_code_m, Sr_top_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem Sr_top_code_d.extend_l {ω m G l H z b w : M.Domain}
    (h : Sr_top_code_d I b G w) (e : Sbuild_d I ω m G l H z) : Sr_top_code_d I b H w := by
  obtain ⟨i, j, a, d, f, t, u, v, hi, hj, ha, hd, hf, ht, hu, hv, hw⟩ := h
  exact ⟨i, j, a, d, f, t, u, v, hi, hj, ha.extend_l I e, hd.extend_l I e, hf.extend_l I e,
    ht.extend_l I e, hu.extend_l I e, hv.extend_l I e, hw.extend_l I e⟩

theorem sr_top_build_l (hZF : M.Models ZF) {ω b m G : M.Domain} (hω : M.IsOmega ω)
    (hb : M.mem b ω) (hG : Sfm_d I ω m G) : ∃ l H w, Sbuild_d I ω m G l H w ∧ Sr_top_code_d I b H w := by
  obtain ⟨i, hi, hiω⟩ := hω.1.2 b hb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 i hiω
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_rel_add_l I hZF hω hG hjω hiω
  obtain ⟨m₂, G₂, h₂, a₂⟩ := sr_rel_add_l I hZF hω h₁.program hjω hb
  obtain ⟨m₃, G₃, h₃, a₃⟩ := sr_nor_add_l I hZF hω h₂.program (h₂.span m h₁.root) (h₂.span m h₁.root)
  obtain ⟨m₄, G₄, h₄, a₄⟩ := sr_nor_add_l I hZF hω h₃.program h₃.root (h₃.span m₁ h₂.root)
  obtain ⟨m₅, G₅, h₅, a₅⟩ := sr_ex_add_l I hZF hω h₄.program hjω h₄.root
  obtain ⟨m₆, G₆, h₆, a₆⟩ := sr_ex_add_l I hZF hω h₅.program hiω h₅.root
  obtain ⟨l, H, h₇, a₇⟩ := sr_nor_add_l I hZF hω h₆.program h₆.root h₆.root
  have e₆ := h₆.comp I h₇
  have e₅ := h₅.comp I e₆
  have e₄ := h₄.comp I e₅
  have e₃ := h₃.comp I e₄
  have e₂ := h₂.comp I e₃
  exact ⟨l, H, m₆, h₁.comp I e₂, i, j, m, m₁, m₂, m₃, m₄, m₅, hi, hj,
    a₁.extend_l I e₂, a₂.extend_l I e₃, a₃.extend_l I e₄, a₄.extend_l I e₅,
    a₅.extend_l I e₆, a₆.extend_l I h₇, a₇⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 最大集合指令的完整语义

两个新变量寻找一个集合及其未被候选最大集合包含的成员。
传递性保证所有反例成员仍在量词域内，故七条指令精确表达最大性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_top_code_d.correct_l (hZF : M.Models ZF) {ω b G m w c Y S D g X : M.Domain}
    (hω : M.IsOmega ω) (hG : Sfm_d I ω m G) (h : Sr_top_code_d I b G w)
    (hm : Smem_d I c Y S) (hY : M.TransitiveSet Y) (hD : M.IsFunctionSpace I D ω Y)
    (hg : M.mem g D) (hx : M.PairMember I b X g) : Ssat_d I Y S D G m w g ↔ Sr_top_d Y X := by
  obtain ⟨i, j, a, d, e, t, u, v, hi, hj, ha, hd, he, ht, hu, hv, hw⟩ := h
  obtain ⟨ca, hca, opa⟩ := ha
  obtain ⟨cd, hcd, opd⟩ := hd
  obtain ⟨ce, hce, ope⟩ := he
  obtain ⟨ct, hct, opt⟩ := ht
  obtain ⟨cu, hcu, opu⟩ := hu
  obtain ⟨cv, hcv, opv⟩ := hv
  obtain ⟨cw, hcw, opw⟩ := hw
  obtain ⟨V, hV⟩ := seval_exists_l I hZF Y S D G hG.2.1.1
  have refs := (hG.2.2 a ca hca).refs_l I (ZF.modelsKP hZF) opa
  have hjOrd := hω.members_areOrdinals (ZF.modelsKP hZF) j refs.1
  have hbj := hjOrd.transitive i hj.predecessor_mem b hi.predecessor_mem
  have ne {x y : M.Domain} (h : M.mem x y) : x ≠ y := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ h)
  have hbi := ne hi.predecessor_mem
  have hbj' := ne hbj
  have hij := ne hj.predecessor_mem
  have fn := (hD g).mp hg
  have hXY := fn.output_mem_of_pairMember hx
  have body A g' B g'' (hA : M.mem A Y) (hB : M.mem B Y)
      (ui : Senv_update_d I g i A g') (uj : Senv_update_d I g' j B g'') :
      Ssat_d I Y S D G m t g'' ↔ M.mem B A ∧ ¬ M.mem B X := by
    have fg := ui.function_l I fn refs.2 hA
    have hg'' := (hD g'').mpr (uj.function_l I fg refs.1 hB)
    have hBv := (uj.2 j B).mpr (Or.inl ⟨rfl, rfl⟩)
    have hAv := (uj.2 i A).mpr (Or.inr ⟨hij, (ui.2 i A).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
    have hXv := (uj.2 b X).mpr (Or.inr ⟨hbj', (ui.2 b X).mpr (Or.inr ⟨hbi, hx⟩)⟩)
    rw [ssat_nor_l I hZF hG hV hct opt hg'', ssat_nor_l I hZF hG hV hce ope hg'',
      ssat_rel_l I hZF hG hV hca opa hD hg'' hBv hAv,
      ssat_rel_l I hZF hG hV hcd opd hD hg'' hBv hXv, hm.2 B A, hm.2 B X]
    simp only [hB, hA, hXY, true_and, or_self, not_or, Classical.not_not]
  have bad : Ssat_d I Y S D G m v g ↔ ∃ A B, M.mem A Y ∧ M.mem B Y ∧ M.mem B A ∧ ¬ M.mem B X := by
    rw [ssat_exists_l I hZF hG hV hcv opv hg]
    constructor
    · rintro ⟨A, g', hA, ui, truth⟩
      have hg' := (hD g').mpr (ui.function_l I fn refs.2 hA)
      obtain ⟨B, g'', hB, uj, truth⟩ := (ssat_exists_l I hZF hG hV hcu opu hg').mp truth
      exact ⟨A, B, hA, hB, (body A g' B g'' hA hB ui uj).mp truth⟩
    · rintro ⟨A, B, hA, hB, hBA, hBX⟩
      obtain ⟨g', ui, fg⟩ := senv_update_exists_l I hZF fn refs.2 hA
      obtain ⟨g'', uj, _⟩ := senv_update_exists_l I hZF fg refs.1 hB
      exact ⟨A, g', hA, ui, (ssat_exists_l I hZF hG hV hcu opu ((hD g').mpr fg)).mpr
        ⟨B, g'', hB, uj, (body A g' B g'' hA hB ui uj).mpr ⟨hBA, hBX⟩⟩⟩
  rw [ssat_nor_l I hZF hG hV hcw opw hg, or_self, bad]
  constructor
  · intro h
    exact ⟨hXY, fun A hA B hBA => Classical.byContradiction fun hn => h ⟨A, B, hA, hY A hA B hBA, hBA, hn⟩⟩
  · rintro h ⟨A, B, hA, _, hBA, hBX⟩
    exact hBX (h.2 A hA B hBA)

end YesMetaZFC.SetTheory.Internal
