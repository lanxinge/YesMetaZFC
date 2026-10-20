import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 源模型包含全部背景内部有限函数

每一步只用配对和并集追加末项，再由外延性识别为背景给定图。
归纳对实际 Fn0 原公式进行，覆盖非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem sc_finite_function_l {ω X A n f : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X)
    (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (union : ∀ a, M.mem a X → ∃ p, M.mem p X ∧ M.IsUnionOf p a)
    (hωX : M.mem ω X) (hA : M.MemberSubset A X) (hn : M.mem n ω) (hf : Fn0_d n A f) : M.mem f X := by
  let ρ := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push X
  let φ : UnarySchema 2 := {
    body := .forallE (.imp (fn0_m (.bound 1) (.bound 3) .newest) (.mem .newest (.bound 2))) }
  have sat n : φ.denote ρ n ↔ ∀ f, Fn0_d n A f → M.mem f X := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      apply (sat z).mpr
      intro f hf
      obtain ⟨e, he, heω⟩ := hω.1.1
      have eq : f = e := hZF.1.eq_of_same_members f e (fun p => iff_of_false
        (fun hp => (hf.1 p hp).elim fun i hi => hz i hi.1) (he p))
      exact eq.symm ▸ hX ω hωX e heω
    · intro n hn ih m hs
      apply (sat m).mpr
      intro f hf
      obtain ⟨g, hg⟩ := ZF.exists_restriction hZF I f n
      have hgn := hg.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hf) (fun i hi => (hs i).mpr (Or.inl hi))
      have hgX := (sat n).mp ih g (fn0_of_function_l (ZF.modelsKP hZF) hgn)
      obtain ⟨x, hx, hnx⟩ := hf.2.1 n hs.predecessor_mem
      have hnX := hX ω hωX n hn
      obtain ⟨s, hsX, singleton⟩ := pair n n hnX hnX
      obtain ⟨t, htX, both⟩ := pair n x hnX (hA x hx)
      obtain ⟨p, hpX, outer⟩ := pair s t hsX htX
      have hp : KPair_d M p n x := ⟨s, t,
        fun y => (singleton y).trans ⟨fun h => h.elim id id, Or.inl⟩, both, outer⟩
      obtain ⟨q, hqX, one⟩ := pair p p hpX hpX
      obtain ⟨r, hrX, two⟩ := pair g q hgX hqX
      obtain ⟨f', hfX, un⟩ := union r hrX
      have graph y : M.mem y f' ↔ M.mem y g ∨ y = p := by
        rw [un]
        exact ⟨fun ⟨z, hz, hy⟩ => ((two z).mp hz).elim
          (fun e => Or.inl (e ▸ hy)) (fun e => Or.inr (((one y).mp (e ▸ hy)).elim id id)),
          fun h => h.elim (fun hy => ⟨g, (two g).mpr (Or.inl rfl), hy⟩)
            (fun e => ⟨q, (two q).mpr (Or.inr rfl), (one y).mpr (Or.inl e)⟩)⟩
      have eq : f' = f := by
        apply hZF.1.eq_of_same_members
        intro y
        rw [graph]
        constructor
        · rintro (hy | rfl)
          · obtain ⟨i, z, code⟩ := hgn.1.1 y hy
            obtain ⟨p', pp, mem⟩ := ((hg.2 i z).mp ⟨y, code, hy⟩).2
            exact kpair_unique_l M hZF.1 pp code ▸ mem
          · obtain ⟨p', pp, mem⟩ := hnx
            exact kpair_unique_l M hZF.1 pp hp ▸ mem
        · intro hy
          obtain ⟨i, hi, z, hz, code⟩ := hf.1 y hy
          rcases (hs i).mp hi with hin | eq
          · obtain ⟨p', pp, mem⟩ := (hg.2 i z).mpr ⟨hin, y, code, hy⟩
            exact Or.inl (kpair_unique_l M hZF.1 pp code ▸ mem)
          · have eq := hZF.1.eq_of_same_members i n eq
            subst i
            have eq := hf.2.2 n hs.predecessor_mem z hz x hx ⟨y, code, hy⟩ hnx
            exact Or.inr (kpair_unique_l M hZF.1 (eq ▸ code) hp)
      exact eq ▸ hfX
  exact (sat n).mp (all n hn) f hf

end YesMetaZFC.SetTheory.Internal
