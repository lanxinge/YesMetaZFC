import YesMetaZFC.SetTheory.InnerModel.Rudimentary.SetImage
import YesMetaZFC.SetTheory.KP.Sigma1Matrix
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded

/-! # 层内 Σ₁ 见证的有限装配

证书同时给出层内传递界和输出。复合、配对只扩大有限次集合界；像运算显式
消费已经给出的共同见证界，不把层内 Σ₁ 收集作为假设或结论。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Si_cert_d {n} (C : M.Domain) (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) : Prop :=
  ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem y B ∧ Formula.satisfies (((ρ.push x).push y).push B) φ.matrix.body

theorem Si_cert_d.sound_l {n} {C : M.Domain} {φ : S1_binary n} {ρ : Env M n} {x y}
    (h : Si_cert_d C φ ρ x y) : φ.schema.denote ρ x y :=
  h.elim fun B h => (φ.sat_l ρ x y).mpr ⟨B, h.2.2.2⟩
theorem Si_cert_d.enclosed_l {n} {C : M.Domain} {φ : S1_binary n} {ρ : Env M n} {x y}
    (h : Si_cert_d C φ ρ x y) : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem y B :=
  h.imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem si_delta_l {n} {C x y : M.Domain} (φ : Delta0BinarySchema n) (ρ : Env M n)
    (hy : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem y B) (h : φ.toBinarySchema.denote ρ x y) :
    Si_cert_d C (S1_binary.of_delta0 φ) ρ x y := by
  obtain ⟨B, hBC, hb, hy⟩ := hy
  exact ⟨B, hBC, hb, hy, (S1_binary.of_delta0_matrix_l φ ρ x y B).mpr h⟩

theorem si_comp_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C) {n}
    {φ ψ : S1_binary n} {ρ : Env M n} {x z y} (h : Si_cert_d C φ ρ x z) (g : Si_cert_d C ψ ρ z y) :
    Si_cert_d C (φ.comp ψ) ρ x y := by
  obtain ⟨B, hBC, hb, hz, h⟩ := h
  obtain ⟨D, hDC, hd, hy, g⟩ := g
  obtain ⟨T, hTC, ht, _, hL⟩ := rd_finite_enclosed_l hKP hC hBC hb [B, D] (by
    intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    exact hX.elim (fun h => h ▸ rd_transitive_enclosed_l hKP hC hBC hb)
      (fun h => h ▸ rd_transitive_enclosed_l hKP hC hDC hd))
  exact ⟨T, hTC, ht, ht D (hL D (by simp)) y hy, (S1_binary.comp_matrix_l φ ψ ρ x y T).mpr
    ⟨z, ht B (hL B (by simp)) z hz, B, hL B (by simp), D, hL D (by simp), h, g⟩⟩

theorem si_pair_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C) {n}
    {φ ψ : S1_binary n} {ρ : Env M n} {x a b p} (h : Si_cert_d C φ ρ x a) (g : Si_cert_d C ψ ρ x b)
    (hp : KPair_d M p a b) : Si_cert_d C (φ.pair ψ) ρ x p := by
  have hpC := rd_fun_enclosed_l hKP hC h.enclosed_l g.enclosed_l h.enclosed_l (rd_opair_value_l hKP.1 hp)
  obtain ⟨B, hBC, hb, ha, h⟩ := h
  obtain ⟨D, hDC, hd, hbD, g⟩ := g
  obtain ⟨T, hTC, ht, _, hL⟩ := rd_finite_enclosed_l hKP hC hBC hb [B, D, p] (by
    intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    exact hX.elim (fun h => h ▸ rd_transitive_enclosed_l hKP hC hBC hb)
      (fun h => h.elim (fun h => h ▸ rd_transitive_enclosed_l hKP hC hDC hd) (fun h => h ▸ hpC)))
  exact ⟨T, hTC, ht, hL p (by simp), (S1_binary.pair_matrix_l hKP.1 φ ψ ρ x p T).mpr
    ⟨a, ht B (hL B (by simp)) a ha, b, ht D (hL D (by simp)) b hbD,
      B, hL B (by simp), D, hL D (by simp), h, g, hp⟩⟩

theorem si_image_l (hKP : M.Models KP) {C B X Y : M.Domain} (hC : Rd_closed_d C)
    (hBC : M.mem B C) (hb : M.TransitiveSet B) (hY : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem Y T)
    {n} (φ : S1_binary n) (ρ : Env M n)
    (h : ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ ∃ w, M.mem w B ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body)
    (g : ∀ y, M.mem y Y → ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) :
    Si_cert_d C φ.image ρ X Y := by
  obtain ⟨T, hTC, ht, bt, hL⟩ := rd_finite_enclosed_l hKP hC hBC hb [Y] (by
    intro A ha; have he := List.mem_singleton.mp ha; exact he ▸ hY)
  refine ⟨T, hTC, ht, hL Y (by simp), (φ.image_matrix_l ρ X Y T).mpr ⟨?_, ?_⟩⟩
  · intro x hx; obtain ⟨y, hy, w, hw, hm⟩ := h x hx; exact ⟨y, hy, w, bt w hw, hm⟩
  · intro y hy; obtain ⟨x, hx, w, hw, hm⟩ := g y hy; exact ⟨x, hx, w, bt w hw, hm⟩

theorem si_bounded_image_l (hKP : M.Models KP) {C B X : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hBC : M.mem B C) (hb : M.TransitiveSet B) (hXC : M.mem X C)
    (hx : M.MemberSubset X B) (φ : S1_binary 0) (ρ : Env M 0) :
    ∃ Y, M.mem Y C ∧ ∀ y, M.mem y Y ↔ M.mem y B ∧
      ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
  obtain ⟨Y, hYC, hy⟩ := rd_bounded_filter_l hKP hC hc hBC hb φ.bounded_image_s ((ρ.push X).push B)
    (Fin.cases ⟨hBC, fun _ h => h⟩ (Fin.cases ⟨hXC, hx⟩ (fun i => Fin.elim0 i)))
  exact ⟨Y, hYC, fun y => (hy y).trans (and_congr_right fun _ => φ.bounded_image_sat_l ρ B X y)⟩

end YesMetaZFC.SetTheory.InnerModel
