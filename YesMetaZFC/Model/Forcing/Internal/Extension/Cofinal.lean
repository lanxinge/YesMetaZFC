import YesMetaZFC.Model.Forcing.Internal.Forcing.Truth
import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence

/-! # 给定泛型滤子的共尾条件列与非反驳判据

只枚举偏序中的条件，不枚举整个地模型。逐次共同加强得到给定滤子内的
共尾下降列；原真值定理把沿任意尾段持续非反驳等同于扩张中的真实成立。
这正是 7.23 中有限一致性约束进入实际泛型解释的步骤。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {P R z : M.Domain} {U : M.Domain → Prop}

theorem Generic_d.cofinal_sequence_l (O : Cond_order_d M P R z) (generic : Generic_d M P R z U)
    (a : Nat → M.Domain) (onto : ∀ p, M.mem p P → ∃ n, a n = p) :
    ∃ q : Nat → M.Domain, (∀ n, U (q n)) ∧
      (∀ n m, n ≤ m → Entry_d M (q m) (q n) R) ∧
      ∀ p, U p → ∀ k, ∃ n, k ≤ n ∧ Entry_d M (q n) p R := by
  classical
  let A := {p : M.Domain // U p}
  have extend (n : Nat) (p : A) : ∃ r : A, Entry_d M r.val p.val R ∧
      (U (a n) → Entry_d M r.val (a n) R) := by
    by_cases hn : U (a n)
    · obtain ⟨r, hr, rp, ra⟩ := generic.directed p.val (a n) p.property hn
      exact ⟨⟨r, hr⟩, rp, fun _ => ra⟩
    · exact ⟨p, O.refl p.val (generic.proper p.val p.property).1, fun h => (hn h).elim⟩
  obtain ⟨p, hp⟩ := generic.inhabited
  let f : Nat → A := Nat.rec ⟨p, hp⟩ (fun n r => Classical.choose (extend n r))
  have step n : Entry_d M (f (n+1)).val (f n).val R ∧
      (U (a n) → Entry_d M (f (n+1)).val (a n) R) := Classical.choose_spec (extend n (f n))
  have mono n m (h : n ≤ m) : Entry_d M (f m).val (f n).val R := by
    induction m with
    | zero =>
      have eq : n = 0 := by omega
      subst n
      exact O.refl _ (generic.proper _ (f 0).property).1
    | succ m ih =>
      by_cases eq : n = m + 1
      · subst n; exact O.refl _ (generic.proper _ (f (m+1)).property).1
      · exact O.trans _ _ _ (generic.proper _ (f (m+1)).property).1
          (generic.proper _ (f m).property).1 (generic.proper _ (f n).property).1 (step m).1 (ih (by omega))
  refine ⟨fun n => (f n).val, fun n => (f n).property, mono, ?_⟩
  intro r hr k
  obtain ⟨n, eq⟩ := onto r (generic.proper r hr).1
  exact ⟨max k (n+1), Nat.le_max_left .., O.trans _ _ _
    (generic.proper _ (f (max k (n+1))).property).1 (generic.proper _ (f (n+1)).property).1
    (generic.proper _ hr).1 (mono _ _ (Nat.le_max_right ..)) (eq ▸ (step n).2 (eq.symm ▸ hr))⟩

variable (O : Cond_order_d M P R z) (hZF : M.Models ZF) (generic : Generic_d M P R z U)
include O generic
local notation "E" => extension_l M hZF P R z U

theorem generic_nonrefute_l {q : Nat → M.Domain} (accepted : ∀ n, U (q n))
    (cofinal : ∀ p, U p → ∀ k, ∃ n, k ≤ n ∧ Entry_d M (q n) p R)
    {d} (φ : Formula 1 d) (hc : φ.FreeClosed) (ρ : Env M d) (η : Env E d)
    (values : Env_val_d hZF ρ η) (k : Nat) :
    Formula.satisfies η φ ↔ ∀ n, k ≤ n → ¬ Forces_d M P R z (.neg φ) ρ (q n) := by
  constructor
  · intro truth n _ forced
    exact ((forcing_truth_l O hZF generic (.neg φ) hc ρ η values).mp ⟨q n, accepted n, forced⟩) truth
  · intro no
    apply Classical.byContradiction
    intro falsehood
    obtain ⟨p, hp, forced⟩ := (forcing_truth_l O hZF generic (.neg φ) hc ρ η values).mpr falsehood
    obtain ⟨n, hn, below⟩ := cofinal p hp k
    exact no n hn ((forces_regular_l O hZF (.neg φ) ρ (env_val_name_l hZF values)).1 p (q n)
      (generic.proper p hp).1 ⟨(generic.proper _ (accepted n)).1, (generic.proper _ (accepted n)).2, below⟩ forced)

/-- 给定可数条件域与实际泛型，一次生成适用于全部原公式、名称赋值和尾段的判据。 -/
theorem Generic_d.nonrefute_sequence_l (a : Nat → M.Domain)
    (onto : ∀ p, M.mem p P → ∃ n, a n = p) :
    ∃ q : Nat → M.Domain, (∀ n, U (q n)) ∧ (∀ n m, n ≤ m → Entry_d M (q m) (q n) R) ∧
      ∀ {d} (φ : Formula 1 d), φ.FreeClosed → ∀ ρ : Env M d, ∀ η : Env E d,
        Env_val_d hZF ρ η → ∀ k, Formula.satisfies η φ ↔
          ∀ n, k ≤ n → ¬ Forces_d M P R z (.neg φ) ρ (q n) := by
  obtain ⟨q, accepted, mono, cofinal⟩ := generic.cofinal_sequence_l O a onto
  exact ⟨q, accepted, mono, fun φ hc ρ η values k => generic_nonrefute_l O hZF generic
    accepted cofinal φ hc ρ η values k⟩

end YesMetaZFC.Model.Forcing.Internal
