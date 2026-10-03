import YesMetaZFC.SetTheory.Descriptive.Projective.CodeCountable
import YesMetaZFC.Model.SetTheory.Internal.Numeral

/-! # 标准有限层数与交替实数量词正规形

Qn_d 是宿主给出的有限个交替量词的展开式，底层是实际 Borel 码。
只在标准数码 Num_d k n 处与内部层对照，不把内部 ω 假定为标准模型。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Qn_d (ω A B J : M.Domain) : Nat → Bool → M.Domain → M.Domain → Prop
  | 0, b, c, x => if b then Bsat_d I ω A A c x else ¬ Bsat_d I ω A A c x
  | k+1, true, c, x => ∃ y z, M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ Qn_d ω A B J k false c z
  | k+1, false, c, x => ∀ y z, M.mem y B → M.mem z B → Rp_d I J x y z → Qn_d ω A B J k true c z

def qn_m : (k : Nat) → (b : Bool) → {d : Nat} → (ω A B J c x : Term d) → Formula 1 d
  | 0, b, _, ω, A, _, _, c, x => if b then bsat_m (𝒞 := 𝒞) ω A A c x else .neg (bsat_m (𝒞 := 𝒞) ω A A c x)
  | k+1, true, _, ω, A, B, J, c, x => .existsE (.existsE (.conj (.mem (.bound 1) B.weaken.weaken) (.conj
      (.mem .newest B.weaken.weaken) (.conj (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest)
      (qn_m k false ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken c.weaken.weaken .newest)))))
  | k+1, false, _, ω, A, B, J, c, x => .forallE (.forallE (.imp (.mem (.bound 1) B.weaken.weaken) (.imp
      (.mem .newest B.weaken.weaken) (.imp (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest)
      (qn_m k true ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken c.weaken.weaken .newest)))))
@[simp] theorem qn_closed_l (k : Nat) (b : Bool) {d} (ω A B J c x : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hB : B.freeSupport = [])
    (hJ : J.freeSupport = []) (hc : c.freeSupport = []) (hx : x.freeSupport = []) :
    (qn_m (𝒞 := 𝒞) k b ω A B J c x).FreeClosed := by
  induction k generalizing b d with
  | zero => cases b <;> simp -implicitDefEqProofs [qn_m, Definitional.Formula.FreeClosed, hω, hA, hc, hx]
  | succ k ih => cases b <;> simp -implicitDefEqProofs [qn_m, Definitional.Formula.FreeClosed, ih, hω, hA, hB, hJ, hc, hx]

theorem qn_sat_l (hE : Extensional M) (k : Nat) (b : Bool) {d} (ρ : Env M d) (ω A B J c x : Term d) :
    Formula.satisfies ρ (qn_m (𝒞 := 𝒞) k b ω A B J c x) ↔
      Qn_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) k b (c.eval ρ) (x.eval ρ) := by
  induction k generalizing b d with
  | zero => cases b <;> simp only [qn_m, Qn_d, Bool.false_eq_true, ↓reduceIte,
      Formula.satisfies_neg_iff, bsat_sat_l I hE]
  | succ k ih => cases b <;> simp only [qn_m, Qn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rp_sat_l I, ih, Definitional.Term.eval_weaken] <;> rfl

theorem qn_dual_l (ω A B J : M.Domain) (k : Nat) (c x : M.Domain) :
    Qn_d I ω A B J k false c x ↔ ¬ Qn_d I ω A B J k true c x := by
  classical
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    constructor
    · intro h ⟨y, z, hy, hz, hp, hn⟩
      exact (ih z).mp hn (h y z hy hz hp)
    · intro h y z hy hz hp
      exact Classical.byContradiction (fun hn => h ⟨y, z, hy, hz, hp, (ih z).mpr hn⟩)

theorem pm_standard_l (hZF : M.Models ZF) {ω A B J k n c x} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Pm_d I ω A B J n c x ↔ M.mem x B ∧ Qn_d I ω A B J k true c x := by
  induction k generalizing n x with
  | zero => exact pm_zero_l I hZF hω hn
  | succ k ih =>
    obtain ⟨m, hm, hnm⟩ := hn
    refine (pm_succ_l I hZF hω (num_mem_l hZF.1 hω hm) hnm).trans (and_congr_right fun _ => ?_)
    apply exists_congr; intro y
    apply exists_congr; intro z
    exact and_congr_right fun _ => and_congr_right fun hz => and_congr_right fun _ =>
      ((not_congr ((ih hm).trans ⟨And.right, fun h => ⟨hz, h⟩⟩)).trans (qn_dual_l I ω A B J k c z).symm)

/-- 标准 Σ¹_k 恰为 k 个交替实数量词作用于 Borel 矩阵所得的集合。 -/
theorem ps_standard_l (hZF : M.Models ZF) {ω A B J k n K} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Ps_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k true c x := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    exact ⟨c, hc, fun x => (pm_mem_l I hZF hω hC hv).trans (pm_standard_l I hZF hω hn)⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
    obtain ⟨L, hL, _⟩ := pval_exists_unique_l I hZF (J := J) hω (num_mem_l hZF.1 hω hn) (fun x hx => ((hC x).mp hx).1)
    have e := hZF.1.eq_of_same_members L K (fun x => (pm_mem_l I hZF hω hC hL).trans
      ((pm_standard_l I hZF hω hn).trans (hk x).symm))
    exact ⟨c, C, hc, hC, e ▸ hL⟩

/-- 标准 Π¹_k 由同长度的全称起始交替式刻画。 -/
theorem pp_standard_l (hZF : M.Models ZF) {ω A B J k n K} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Pp_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k false c x := by
  constructor
  · rintro ⟨L, hl, hk⟩
    obtain ⟨c, hc, hv⟩ := (ps_standard_l I hZF hω hn).mp hl
    exact ⟨c, hc, fun x => (hk x).trans (and_congr_right fun hx =>
      (not_congr ((hv x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).trans (qn_dual_l I ω A B J k c x).symm)⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨L, hl⟩ := cm_exists_l (ZF.modelsKP hZF) B K
    have sub : M.MemberSubset K B := fun x hx => ((hk x).mp hx).1
    refine ⟨L, (ps_standard_l I hZF hω hn).mpr ⟨c, hc, fun x => ?_⟩, cm_symm_l sub hl⟩
    classical
    refine (hl x).trans (and_congr_right fun hx => ?_)
    simpa only [Classical.not_not] using
      (not_congr (((hk x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩).trans (qn_dual_l I ω A B J k c x)))

/-- 对每个标准 k 实际给出唯一内部层号，并同时返回 Σ、Π 的对应。 -/
theorem standard_level_l (hZF : M.Models ZF) {ω A B J} (hω : M.IsOmega ω) (k : Nat) :
    ∃ n, Num_d k n ∧ M.mem n ω ∧ (∀ m, Num_d k m → m = n) ∧ ∀ K,
      (Ps_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k true c x) ∧
      (Pp_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k false c x) := by
  obtain ⟨n, hn⟩ := num_exists_l (ZF.modelsKP hZF) k
  exact ⟨n, hn, num_mem_l hZF.1 hω hn, fun _ h => num_unique_l hZF.1 h hn,
    fun _ => ⟨ps_standard_l I hZF hω hn, pp_standard_l I hZF hω hn⟩⟩

end YesMetaZFC.SetTheory.Descriptive
