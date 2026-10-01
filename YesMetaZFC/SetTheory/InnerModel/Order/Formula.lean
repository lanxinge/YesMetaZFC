import YesMetaZFC.SetTheory.InnerModel.Order.Successor
import YesMetaZFC.SetTheory.KP.Finite

/-! # 规范扩张的有界集合图

参数域、函数像和关系表均双向检查，防止证书只记录截断的输出。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rw_domain_m {n} (U P : Term n) : Formula 1 n :=
  .conj (Formula.forallMem P (Formula.existsMem U.weaken (Formula.existsMem U.weaken.weaken
    (Formula.existsMem U.weaken.weaken.weaken (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest)))))
    (Formula.forallMem U (Formula.forallMem U.weaken (Formula.forallMem U.weaken.weaken
      (Formula.existsMem P.weaken.weaken.weaken (rd_triple0_m .newest (.bound 3) (.bound 2) (.bound 1))))))
derive_free_closed rw_domain_m
theorem rw_domain_delta_l {n} (U P : Term n) : (rw_domain_m U P).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (.existsMem _ (rd_triple0_delta_l ..)))))
    (.forallMem _ (.forallMem _ (.forallMem _ (.existsMem _ (rd_triple0_delta_l ..)))))
theorem rw_domain_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (U P : Term n) :
    Formula.satisfies ρ (rw_domain_m U P) ↔ Rw_domain_d (U.eval ρ) (P.eval ρ) := by
  simp only [rw_domain_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_triple0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g⟩ p
    refine ⟨h p, fun ⟨a, ha, b, hb, c, hc, hp⟩ => ?_⟩
    obtain ⟨q, hq, he⟩ := g a ha b hb c hc
    exact pn_triple_unique_l hKP.1 he hp ▸ hq
  · intro h
    refine ⟨fun p => (h p).mp, fun a ha b hb c hc => ?_⟩
    obtain ⟨q, hq⟩ := (kp_pair_l hKP).total b c
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total a q
    exact ⟨p, (h p).mpr ⟨a, ha, b, hb, c, hc, q, hq, hp⟩, q, hq, hp⟩

def rw_image_m {n} (k : Rd_sym) (U P Y : Term n) : Formula 1 n :=
  .conj (Formula.forallMem Y (Formula.existsMem P.weaken (rw_fun_m k U.weaken.weaken .newest (.bound 1))))
    (Formula.forallMem P (Formula.existsMem Y.weaken (rw_fun_m k U.weaken.weaken (.bound 1) .newest)))
derive_free_closed rw_image_m
theorem rw_image_delta_l {n} (k : Rd_sym) (U P Y : Term n) : (rw_image_m k U P Y).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (rw_fun_delta_l ..))) (.forallMem _ (.existsMem _ (rw_fun_delta_l ..)))
theorem rw_image_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (U P Y : Term n)
    (hp : Rw_domain_d (U.eval ρ) (P.eval ρ)) :
    Formula.satisfies ρ (rw_image_m k U P Y) ↔ Rw_image_d k (U.eval ρ) (P.eval ρ) (Y.eval ρ) := by
  simp only [rw_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rw_fun_formula_l hKP, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g⟩ x
    refine ⟨h x, fun ⟨p, hp, hx⟩ => ?_⟩
    obtain ⟨y, hy, he⟩ := g p hp
    exact rw_fun_unique_l hKP.1 he hx ▸ hy
  · intro h
    exact ⟨fun x => (h x).mp, fun p hpP => (rw_fun_total_l hKP k ((hp p).mp hpP)).elim
      (fun x hx => ⟨x, (h x).mpr ⟨p, hpP, hx⟩, hx⟩)⟩

def rw_table_s {n} (φ : Delta0BinarySchema n) : Delta0BinarySchema n where
  body := .conj (Formula.forallMem .newest (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
      (binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) .newest)))))
    (Formula.forallMem (.bound 1) (Formula.forallMem (.bound 2)
      (.imp (binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 4, by omega⟩) (.bound 1) .newest)
        (rd_entry0_m (.bound 1) .newest (.bound 2)))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .conj (.forallMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (φ.delta0.bind_l _)))))
    (.forallMem _ (.forallMem _ (.imp (φ.delta0.bind_l _) (rd_entry0_delta_l ..))))
theorem rw_table_sat_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X S : M.Domain) :
    (rw_table_s φ).toBinarySchema.denote ρ X S ↔ Rw_rel_d (φ.toBinarySchema.denote ρ) X S := by
  simp only [BinarySchema.denote, rw_table_s, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, binary_pred_sat_l]
  change ((∀ p, M.mem p S → ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧ KPair_d M p x y ∧ φ.toBinarySchema.denote ρ x y) ∧
    ∀ x, M.mem x X → ∀ y, M.mem y X → φ.toBinarySchema.denote ρ x y → Rd_entry_d x y S) ↔ _
  constructor
  · rintro ⟨h, g⟩ p
    refine ⟨h p, fun ⟨x, hx, y, hy, hp, hxy⟩ => ?_⟩
    obtain ⟨q, hq, hqS⟩ := g x hx y hy hxy
    exact kpair_unique_l M hKP.1 hq hp ▸ hqS
  · intro h
    exact ⟨fun p => (h p).mp, fun x hx y hy hxy => (h.entry_l hKP).mpr ⟨hx, hy, hxy⟩⟩

def rw_table_m {n} (φ : Delta0BinarySchema 3) (a b c X S : Term n) : Formula 1 n :=
  binary_pred_m (rw_table_s φ).toBinarySchema (fun i => if i.val = 0 then a else if i.val = 1 then b else c) X S
@[simp] theorem rw_table_closed_l {n} (φ : Delta0BinarySchema 3) (a b c X S : Term n)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) (hc : c.freeSupport = [])
    (hX : X.freeSupport = []) (hS : S.freeSupport = []) : (rw_table_m φ a b c X S).FreeClosed := by
  apply binary_pred_closed_l _ _ _ _ _ hX hS
  intro i; split <;> first | assumption | split <;> assumption
theorem rw_table_delta_l {n} (φ : Delta0BinarySchema 3) (a b c X S : Term n) :
    (rw_table_m φ a b c X S).IsDelta0 := (rw_table_s φ).delta0.bind_l _
theorem rw_table_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (φ : Delta0BinarySchema 3) (a b c X S : Term n) :
    Formula.satisfies ρ (rw_table_m φ a b c X S) ↔ Rw_rel_d
      (φ.toBinarySchema.denote ⟨fun i => (if i.val = 0 then a else if i.val = 1 then b else c).eval ρ, ρ.free⟩) (X.eval ρ) (S.eval ρ) := by
  rw [rw_table_m, binary_pred_sat_l, rw_table_sat_l hKP]

def rw_union_m {n} (V A B : Term n) : Formula 1 n := .conj (Formula.subset A V)
  (.conj (Formula.subset B V) (Formula.forallMem V (.disj (.mem .newest A.weaken) (.mem .newest B.weaken))))
derive_free_closed rw_union_m
theorem rw_union_delta_l {n} (V A B : Term n) : (rw_union_m V A B).IsDelta0 :=
  .conj (.atom _ _ _) (.conj (.atom _ _ _) (.forallMem _ (.disj (.mem _ _) (.mem _ _))))
theorem rw_union_sat_l {n} (ρ : Env M n) (V A B : Term n) :
    Formula.satisfies ρ (rw_union_m V A B) ↔ M.IsUnionOfTwo (V.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [rw_union_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨h, g, f⟩ x => ⟨f x, fun hx => hx.elim (h x) (g x)⟩,
    fun h => ⟨fun x hx => (h x).mpr (Or.inl hx), fun x hx => (h x).mpr (Or.inr hx), fun x => (h x).mp⟩⟩

end YesMetaZFC.SetTheory.InnerModel
