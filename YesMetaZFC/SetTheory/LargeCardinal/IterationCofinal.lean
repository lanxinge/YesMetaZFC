import YesMetaZFC.SetTheory.LargeCardinal.IterationBranch
import YesMetaZFC.SetTheory.OrdinalChoice
import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.Cofinality.Basic

/-! # 可数共尾长度上实际选择一条共尾树枝

每个结点若都有任意高的树后继，就沿给定内部 ω 共尾序列逐项越过高度。
每步选最小可用序数，确定递归只用 ZF；最后取所得链的树序向下闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_cofinal_branch_l {ω α T F a : M.Domain} (hω : M.IsOmega ω) (h : It_order_d α T)
    (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j)) :
    ∃ B, It_branch_d α T B ∧ M.mem a B := by
  have seq := cf.isIncreasing.1.1
  have ff : M.IsSetFunctionFromTo I F ω α := ⟨seq.2.1, seq.2.2, fun n hn => by
    obtain ⟨k, hk⟩ := (seq.2.2 n).mp hn
    exact ⟨k, cf.value_mem hn hk, hk⟩⟩
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I ω α
  let φ : BinarySchema 2 := { body := .existsE (.existsE (.conj
    (kpair_m (.bound 3) (.bound 1) .newest) (.conj (rd_entry_m .newest (.bound 2) (.bound 5))
      (.forallE (.imp (rd_entry_m (.bound 2) .newest (.bound 5))
        (.disj (Formula.extensionalEq .newest (.bound 3)) (.mem .newest (.bound 3)))))))) }
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => T), fun _ => a⟩
  have sat p y : φ.denote ρ p y ↔ ∃ n x, KPair_d M p n x ∧ Rd_entry_d x y T ∧
      ∀ k, Rd_entry_d n k F → k = y ∨ M.mem k y := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, rd_entry_sat_l hZF.1, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_mem_iff]; rfl
  obtain ⟨K, hk, ks⟩ := ZF.ordinal_uniformize_l hZF φ ρ (D := D) h.ordinal (by
    intro p hp
    obtain ⟨n, hn, x, hx, hp⟩ := (hd p).mp hp
    obtain ⟨k, hka, hnk⟩ := ff.2.2 n hn
    obtain ⟨y, _, hxy, above⟩ := pruned x k hx hka
    exact ⟨y, (sat p y).mpr ⟨n, x, hp, hxy, fun k' hnk' => ff.1.2 n k' k hnk' hnk ▸ above⟩⟩) (by
    intro p y _ hy
    obtain ⟨_, x, _, hxy, _⟩ := (sat p y).mp hy
    exact (h.bound x y hxy).2)
  obtain ⟨g, hg, start, step⟩ := ZF.indexed_iteration_l I hZF hω hd (fn0_function_l (ZF.modelsKP hZF) hk) ha
  have advance n m x y (hm : M.SuccessorOf m n) (hx : Rd_entry_d n x g) (hy : Rd_entry_d m y g) :
      Rd_entry_d x y T ∧ ∀ k, Rd_entry_d n k F → k = y ∨ M.mem k y := by
    obtain ⟨p, hp, hpy⟩ := step n m x y hm hx hy
    obtain ⟨n', x', hp', hxy, above⟩ := (sat p y).mp (ks p y hpy)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact ⟨hxy, above⟩
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  let η : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  have psat x y : ψ.denote η x y ↔ Rd_entry_d x y T := rd_entry_sat_l hZF.1 ..
  have chain n m x y (hnm : M.mem n m) (hx : Rd_entry_d n x g) (hy : Rd_entry_d m y g) : Rd_entry_d x y T :=
    (psat x y).mp (ZF.rel_chain_l I hZF ψ η hω hg
      (fun x y z _ _ _ hx hy => (psat x z).mpr (h.trans x y z ((psat x y).mp hx) ((psat y z).mp hy)))
      (fun n m x y hm hx hy => (psat x y).mpr (advance n m x y hm hx hy).1) n m x y hnm hx hy)
  let χ : UnarySchema 2 := { body := .existsE (.existsE
    (.conj (rd_entry_m (.bound 1) .newest (.bound 3)) (rd_entry_m (.bound 2) .newest (.bound 4)))) }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases g (fun _ => T), fun _ => T⟩ α
  have read i : M.mem i B ↔ M.mem i α ∧ ∃ n x, Rd_entry_d n x g ∧ Rd_entry_d i x T := by
    simpa only [χ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1] using! bs i
  have points n x (hx : Rd_entry_d n x g) : M.mem x B :=
    (read x).mpr ⟨hg.output_mem_of_pairMember hx, n, x, hx, h.refl x (hg.output_mem_of_pairMember hx)⟩
  have comparable i j (hi : M.mem i B) (hj : M.mem j B) : Rd_entry_d i j T ∨ Rd_entry_d j i T := by
    obtain ⟨_, n, x, hx, hix⟩ := (read i).mp hi
    obtain ⟨_, m, y, hy, hjy⟩ := (read j).mp hj
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare n (hg.input_mem_of_pairMember hx) m (hg.input_mem_of_pairMember hy) with eq | hnm | hmn
    · have eq := hZF.1.eq_of_same_members n m eq
      subst m
      have eq := hg.1.2 n x y hx hy
      exact h.chain i j y (eq ▸ hix) hjy
    · exact h.chain i j y (h.trans i x y hix (chain n m x y hnm hx hy)) hjy
    · exact h.chain i j x hix (h.trans j y x hjy (chain m n y x hmn hy hx))
  have cofinal i (hi : M.mem i α) : ∃ j, M.mem j B ∧ (i = j ∨ M.mem i j) := by
    obtain ⟨D, hd⟩ := ZF.exists_range_of_setFunction hZF I ff.1 ff.2.1
    obtain ⟨k, hk, hik⟩ := ((cf.range_isCofinalSubset hZF.1 hd).2.2 i).mp hi
    obtain ⟨n, hnk⟩ := (hd k).mp hk
    have hn := ff.input_mem_of_pairMember hnk
    obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
    obtain ⟨x, _, hx⟩ := hg.2.2 n hn
    obtain ⟨y, hyα, hy⟩ := hg.2.2 m hmω
    refine ⟨y, points m y hy, Or.inr ?_⟩
    rcases (advance n m x y hm hx hy).2 k hnk with rfl | hky
    · exact hik
    · exact (h.ordinal.mem hyα).transitive k hky i hik
  obtain ⟨z, hz, _⟩ := hω.1.1
  exact ⟨B, ⟨fun i hi => ((read i).mp hi).1, comparable, fun i j hij hj => by
    obtain ⟨_, n, x, hx, hjx⟩ := (read j).mp hj
    exact (read i).mpr ⟨(h.bound i j hij).1, n, x, hx, h.trans i j x hij hjx⟩, cofinal⟩,
    points z a (start z hz)⟩

end YesMetaZFC.SetTheory.LargeCardinal
