import YesMetaZFC.Model.SetTheory.Internal.SourceFinite

/-! # 有限定义域上的部分图属于源

先在有限序数上补成总图，再用源内定义域取回原限制。只使用已有有限函数
闭性及有界分离，不假定源对任意外部子集封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_finite_partial_l {ω c X R D n f : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hωX : M.mem ω X) (hD : M.mem D X) (hn : M.mem n ω) (sub : M.MemberSubset D n)
    (hf : Fn0_d D X f) : M.mem f X := by
  let ρ : Env M 3 := ⟨Fin.cases D (Fin.cases f (fun _ => ω)), fun _ => ω⟩
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3)))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 4))) }
  have read a b : φ.denote ρ a b ↔ (M.mem a D ∧ Rd_entry_d a b f) ∨ (¬ M.mem a D ∧ b = ω) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨g, fg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := X)
    (fun a _ => by
      classical
      by_cases ha : M.mem a D
      · obtain ⟨b, _, hb⟩ := hf.2.1 a ha
        exact ⟨b, (read a b).mpr (Or.inl ⟨ha, hb⟩)⟩
      · exact ⟨ω, (read a ω).mpr (Or.inr ⟨ha, rfl⟩)⟩)
    (fun a _ b c hb hc => by
      rcases (read a b).mp hb with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        rcases (read a c).mp hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · exact (fn0_function_l (ZF.modelsKP hZF) hf).1.2 a b c hb hb'
      · exact (ha' ha).elim
      · exact (ha ha').elim
      · exact hb.trans hb'.symm)
    (fun a b _ hb => ((read a b).mp hb).elim (fun h => (hf.bound_l h.2).2) (fun h => h.2.symm ▸ hωX))
  have hg := sc_finite_function_l hZF hω hX theory.algebra.pair theory.algebra.union hωX (fun _ h => h) hn (fn0_of_function_l (ZF.modelsKP hZF) fg)
  obtain ⟨C, hC, bound⟩ := theory.algebra.envelope_l hg
  let η : Env M 2 := ⟨Fin.cases D (fun _ => C), fun _ => D⟩
  let ψ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)) }
  have ps p : ψ.denote η p ↔ ∃ a, M.mem a D ∧ ∃ b, M.mem b C ∧ KPair_d M p a b := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨q, hq, qs⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) η (Fin.cases hD (fun _ => hC)) hg
  have eq : q = f := hZF.1.eq_of_same_members q f fun p => by
    constructor
    · intro hp
      obtain ⟨hp, hs⟩ := (qs p).mp hp
      obtain ⟨a, ha, b, _, pair⟩ := (ps p).mp hs
      have hb : Rd_entry_d a b f := ((read a b).mp ((spec a b).mp ⟨p, pair, hp⟩).2).elim And.right (fun h => (h.1 ha).elim)
      obtain ⟨r, hr, hrf⟩ := hb
      exact kpair_unique_l M hZF.1 hr pair ▸ hrf
    · intro hp
      obtain ⟨a, ha, b, _, pair⟩ := hf.1 p hp
      have hb := (spec a b).mpr ⟨sub a ha, (read a b).mpr (Or.inl ⟨ha, p, pair, hp⟩)⟩
      have hbc := (bound a b hb).2
      obtain ⟨r, hr, hrg⟩ := hb
      exact (qs p).mpr ⟨kpair_unique_l M hZF.1 hr pair ▸ hrg, (ps p).mpr ⟨a, ha, b, hbc, pair⟩⟩
  exact eq ▸ hq

end YesMetaZFC.SetTheory.Internal
