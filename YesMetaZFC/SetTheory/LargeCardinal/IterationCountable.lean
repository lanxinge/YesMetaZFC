import YesMetaZFC.SetTheory.LargeCardinal.IterationTree
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCountable
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead
import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 可数根的 ω 长迭代树全部模型可数

内部归纳同时保留所有较早结点的计数界。活动步只读取原树指定的超幂，
其支撑是所属模型的一个成员；padding 则保留原模型。最后实际收集公共可数载体。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_l {ω c₀ T Q G E X₀ R₀ : M.Domain}
    (tree : It_tree_d hZF ω c₀ ω T Q G E) (mx : Smdl_d I c₀ X₀ R₀) (cx : M.CardinalLessOrEqual I X₀ ω) :
    ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω := by
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ i, (i = ⌜(Term.newest : Term 3)⌝ₛ ∨ i ∈ ⌜(Term.newest : Term 3)⌝ₛ) →
    ∀ c X R, ⌜rd_entry0_m⌝ₚ(i, c, ⌜(Term.bound 1 : Term 3)⌝ₛ) → ⌜kpair_m⌝ₚ(c, X, R) →
      ∃ f, ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(f, X, ⌜(Term.bound 2 : Term 3)⌝ₛ)⟫ }
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => ω), fun _ => ω⟩
  have sat n : φ.denote ρ n ↔ ∀ i, i = n ∨ M.mem i n →
      ∀ c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hZF.1, kpair_sat_l M hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_isInjectionFromTo_iff I hZF.1, Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply tree.omega.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      apply (sat z).mpr
      intro i hi c X R hc hp
      rcases hi with eq | hi
      · subst i
        have ec := tree.diagram.model_function.2 z c c₀ hc (tree.root z hz)
        obtain ⟨ex, _⟩ := kpair_injective_l M (ec ▸ hp) mx.1
        exact ex.symm ▸ cx
      · exact (hz i hi).elim
    · intro n hn ih m hm
      have hmω : M.mem m ω := by
        obtain ⟨m', hm', hm'ω⟩ := tree.omega.1.2 n hn
        exact Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hm'ω
      have old i (hi : M.mem i m) := (sat n).mp ih i (((hm i).mp hi).elim Or.inr
        (fun eq => Or.inl (hZF.1.eq_of_same_members i n eq)))
      apply (sat m).mpr
      intro i hi c X R hc hp
      rcases hi with eq | hi
      · subst i
        obtain ⟨k, a, d, b, f, p, pred, ha, hd, hb, _, _, step⟩ := tree.steps n m hmω hm
        have ec := tree.diagram.model_function.2 m b c hb hc
        subst b
        rcases step with ⟨_, _, same, _⟩ | ⟨κ, L, F, N, S, Y, V, _, mn, my, loc, _, edge⟩
        · exact (sat n).mp ih n (Or.inl rfl) a X R ha (same ▸ hp)
        · obtain ⟨N', S', K, mn', owner⟩ := tree.sources n a ha
          obtain ⟨en, es⟩ := smdl_unique_l I mn'.1 mn.1
          subst N' S'
          obtain ⟨j, hj⟩ := ZF.exists_inclusionInjection hZF I (owner.transitive L loc.2.2.1)
          obtain ⟨v, hv⟩ := (sat n).mp ih n (Or.inl rfl) a N S ha mn.1.1
          have cl := ZF.exists_compositionInjection hZF I hj hv
          obtain ⟨X', R', mt⟩ := tree.diagram.models m c hc
          obtain ⟨ex, er⟩ := kpair_injective_l M mt.1 hp
          subst X' R'
          exact edge.countable_l hZF tree.omega (loc.function_l hZF owner.transitive owner.theory.algebra.pair)
            (old k pred.1 d Y V hd my.1.1) cl my.1 mt
      · exact old i hi c X R hc hp
  exact fun i c X R hc hp => (sat i).mp (all i ((tree.diagram.model_domain i).mpr ⟨c, hc⟩)) i (Or.inl rfl) c X R hc hp

end YesMetaZFC.SetTheory.LargeCardinal
