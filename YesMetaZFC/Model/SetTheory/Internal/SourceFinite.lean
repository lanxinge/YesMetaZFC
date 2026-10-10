import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 源模型包含全部背景内部有限函数

每一步在源内统一构造追加末项后的函数图，再由唯一性识别为背景给定图。
归纳对实际 Fn0 原公式进行，覆盖非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_finite_function_l {ω c X R A n f : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
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
      obtain ⟨m', hs', hm'⟩ := hω.1.2 n hn
      have hmω := Structure.SuccessorOf.eq hZF.1 hs' hs ▸ hm'
      let η := ((⟨fun _ => n, fun _ => n⟩ : Env M 1).push g).push x
      let ψ : BinarySchema 3 := {
        body := .disj (.conj (.mem (.bound 1) (.bound 4)) (rd_entry0_m (.bound 1) .newest (.bound 3)))
          (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.extensionalEq .newest (.bound 2))) }
      have read i y : ψ.denote η i y ↔ (M.mem i n ∧ Rd_entry_d i y g) ∨ (¬ M.mem i n ∧ y = x) := by
        simp only [ψ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
          Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1,
          Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
      obtain ⟨B, hBX, bound⟩ := theory.algebra.envelope_l hgX
      obtain ⟨C, hCX, hc⟩ := theory.algebra.insert_l hBX (hA x hx)
      obtain ⟨f', hfX, hfn, choose⟩ := sc_uniform_source_l hZF hω hX hm theory ψ
        (.disj (.conj (.mem _ _) (rd_entry0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom _ _ _))) η
        (Fin.cases (hA x hx) (Fin.cases hgX (fun _ => hX ω hωX n hn))) (hX ω hωX m hmω)
        hCX (fun i _ => by
          classical
          by_cases hi : M.mem i n
          · obtain ⟨y, _, hiy⟩ := hgn.2.2 i hi
            exact ⟨y, (hc y).mpr (Or.inl (bound i y hiy).2), (read i y).mpr (Or.inl ⟨hi, hiy⟩)⟩
          · exact ⟨x, (hc x).mpr (Or.inr rfl), (read i x).mpr (Or.inr ⟨hi, rfl⟩)⟩)
      have eq : f' = f := hfn.ext_l hZF.1 hf (fun i hi => by
        obtain ⟨y, _, hiy⟩ := hfn.2.1 i hi
        refine ⟨y, hiy, ?_⟩
        rcases (read i y).mp (choose i y hiy) with ⟨_, h⟩ | ⟨hn, rfl⟩
        · exact ((hg.2 i y).mp h).2
        · have eq := ((hs i).mp hi).elim (fun h => (hn h).elim) (hZF.1.eq_of_same_members i n)
          exact eq.symm ▸ hnx)
      exact eq ▸ hfX
  exact (sat n).mp (all n hn) f hf

end YesMetaZFC.SetTheory.Internal
