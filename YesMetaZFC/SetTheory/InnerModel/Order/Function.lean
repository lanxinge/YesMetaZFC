import YesMetaZFC.SetTheory.InnerModel.Order.Tuple
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph

/-! # 实际 rud 运算的有界最小生成参数

参数域固定为 U³，值域和同值纤维均由 Δ₀ 替换、分离取得。
最小原像使用输入良序的三元字典序，不使用全局 J 良序。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_fun_d (k : Rd_sym) (U p x : M.Domain) : Prop := ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧
  Rd_triple_d p a b c ∧ Rd_fun_d k a b c x
def rw_fun_s (k : Rd_sym) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
    .conj (rd_triple0_m (.bound 4) (.bound 2) (.bound 1) .newest) (rd_graph_m k (.bound 2) (.bound 1) .newest (.bound 3))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..) (rd_graph_delta_l ..))))
theorem rw_fun_sat_l (hKP : M.Models KP) (k : Rd_sym) (ρ : Env M 1) (p x : M.Domain) :
    (rw_fun_s k).toBinarySchema.denote ρ p x ↔ Rw_fun_d k (ρ.bound 0) p x := by
  simp only [BinarySchema.denote, rw_fun_s, Rw_fun_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hKP.1, rd_graph_sat_l hKP]; rfl
def rw_fun_m {n} (k : Rd_sym) (U p x : Term n) : Formula 1 n := binary_pred_m (rw_fun_s k).toBinarySchema (fun _ => U) p x
derive_free_closed rw_fun_m
theorem rw_fun_delta_l {n} (k : Rd_sym) (U p x : Term n) : (rw_fun_m k U p x).IsDelta0 := (rw_fun_s k).delta0.bind_l _
theorem rw_fun_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (U p x : Term n) :
    Formula.satisfies ρ (rw_fun_m k U p x) ↔ Rw_fun_d k (U.eval ρ) (p.eval ρ) (x.eval ρ) := by
  rw [rw_fun_m, binary_pred_sat_l, rw_fun_sat_l hKP]

theorem rw_fun_total_l (hKP : M.Models KP) (k : Rd_sym) {U p : M.Domain} (hp : Rw_tuple_d U p) : ∃ x, Rw_fun_d k U p x := by
  obtain ⟨a, ha, b, hb, c, hc, hp⟩ := hp
  obtain ⟨x, hx⟩ := rd_fun_exists_l hKP k a b c
  exact ⟨x, a, ha, b, hb, c, hc, hp, hx⟩
theorem rw_fun_unique_l (hE : Extensional M) {k U p x y} (hx : Rw_fun_d (M := M) k U p x) (hy : Rw_fun_d k U p y) : x = y := by
  obtain ⟨a, _, b, _, c, _, hp, hx⟩ := hx
  obtain ⟨a', _, b', _, c', _, hq, hy⟩ := hy
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hq hp
  exact rd_fun_unique_l hE hx hy

def Rw_image_d (k : Rd_sym) (U P Y : M.Domain) : Prop := ∀ x, M.mem x Y ↔ ∃ p, M.mem p P ∧ Rw_fun_d k U p x
theorem rw_image_exists_l (hKP : M.Models KP) (k : Rd_sym) {U P : M.Domain} (hp : Rw_domain_d U P) : ∃ Y, Rw_image_d k U P Y := by
  let ρ : Env M 1 := ⟨fun _ => U, fun _ => U⟩
  obtain ⟨Y, hy⟩ := KP.d0_image_l hKP (rw_fun_s k) ρ P
    (fun p hpP => (rw_fun_total_l hKP k ((hp p).mp hpP)).imp (fun x hx => (rw_fun_sat_l hKP k ρ p x).mpr hx))
    (fun p _ x y hx hy => rw_fun_unique_l hKP.1 ((rw_fun_sat_l hKP k ρ p x).mp hx) ((rw_fun_sat_l hKP k ρ p y).mp hy))
  exact ⟨Y, fun x => (hy x).trans (exists_congr fun p => and_congr_right fun _ => rw_fun_sat_l hKP k ρ p x)⟩

def Rw_min_d (k : Rd_sym) (U R P p x : M.Domain) : Prop := M.mem p P ∧ Rw_fun_d k U p x ∧
  ∀ q, M.mem q P → Rw_lex_d U R q p → ¬ Rw_fun_d k U q x
def rw_min_m {n} (k : Rd_sym) (U R P p x : Term n) : Formula 1 n := .conj (.mem p P) (.conj (rw_fun_m k U p x)
  (Formula.forallMem P (.imp (rw_lex_m U.weaken R.weaken .newest p.weaken) (.neg (rw_fun_m k U.weaken .newest x.weaken)))))
derive_free_closed rw_min_m
theorem rw_min_delta_l {n} (k : Rd_sym) (U R P p x : Term n) : (rw_min_m k U R P p x).IsDelta0 :=
  .conj (.mem _ _) (.conj (rw_fun_delta_l ..) (.forallMem _ (.imp (rw_lex_delta_l ..) (.neg (rw_fun_delta_l ..)))))
theorem rw_min_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (U R P p x : Term n) :
    Formula.satisfies ρ (rw_min_m k U R P p x) ↔ Rw_min_d k (U.eval ρ) (R.eval ρ) (P.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [rw_min_m, Rw_min_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rw_fun_formula_l hKP,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rw_lex_formula_l hKP.1, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem rw_min_exists_l (hKP : M.Models KP) {U R P x : M.Domain} {k}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hx : ∃ p, M.mem p P ∧ Rw_fun_d k U p x) : ∃ p, Rw_min_d k U R P p x := by
  let ρ : Env M 2 := (⟨fun _ => U, fun _ => U⟩ : Env M 1).push x
  let φ : Delta0UnarySchema 2 := { body := rw_fun_m k (.bound 2) .newest (.bound 1), delta0 := rw_fun_delta_l .. }
  obtain ⟨X, hX⟩ := KP.separation_exists_d hKP φ ρ P
  have spec p : M.mem p X ↔ M.mem p P ∧ Rw_fun_d k U p x := (hX p).trans (and_congr_right fun _ => rw_fun_formula_l hKP _ _ _ _ _)
  obtain ⟨p, hpX, hm⟩ := rw_lex_min_l hKP hr (fun p hpX => (hp p).mp ((spec p).mp hpX).1)
    (hx.imp (fun p h => (spec p).mpr h))
  refine ⟨p, ((spec p).mp hpX).1, ((spec p).mp hpX).2, fun q hq hqp hqx => ?_⟩
  rcases hm q ((spec q).mpr ⟨hq, hqx⟩) with he | he
  · subst q; exact rw_lex_irrefl_l hKP hr hqp
  · exact rw_lex_irrefl_l hKP hr (rw_lex_trans_l hKP hr he hqp)

theorem rw_min_unique_l (hKP : M.Models KP) {U R P p q x : M.Domain} {k}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hx : Rw_min_d k U R P p x) (hy : Rw_min_d k U R P q x) : p = q := by
  rcases rw_lex_compare_l hKP hr ((hp p).mp hx.1) ((hp q).mp hy.1) with he | he | he
  · exact he
  · exact (hy.2.2 p hx.1 he hx.2.1).elim
  · exact (hx.2.2 q hy.1 he hy.2.1).elim

end YesMetaZFC.SetTheory.InnerModel
