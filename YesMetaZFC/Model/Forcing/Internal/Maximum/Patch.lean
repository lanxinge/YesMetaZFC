import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool

/-! # 在固定名称库内修补局部见证

若 s 只在部分条件下满足 φ，则在这些条件上保留 s，在迫使 ¬φ(s) 的条件上
使用已有的全局见证 t。两类条件不能相容，故实际混合仍属于同一名称库。
这使稠密集的局部名称变成全局稠密集名称，而不改变它在给定泛型中的值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z s t W : M.Domain}

theorem name_pool_patch_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {n} (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i))
    {v w} (pool : Name_pool_d M B v w W) (hs : M.mem s W) (ht : M.mem t W)
    (fallback : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push t) p) :
    ∃ a, M.mem a W ∧
      (∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push a) p) ∧
      ∀ p, M.mem p B → Forces_d M B R z φ.body (ρ.push s) p → Eq_force_d M B R z p a s := by
  classical
  have hn x (hx : M.mem x W) : Name_d M B x := ⟨W, hx, pool.closed⟩
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  have change_env x p := forces_env_l (B := B) (R := R) (z := z) hZF.1
    φ.body φ.freeClosed (ρ.push x) (η.push x) (fun _ => rfl) p
  have reg x (hx : M.mem x W) := forces_regular_l O hZF φ.body (η.push x) (by
    intro a
    cases a with
    | free _ => exact hn s hs
    | bound i => exact Fin.cases (hn x hx) hρ i)
  let δ := ((((η.push B).push R).push z).push s).push t
  let es : Fin (n+1) → Term (n+7) := Fin.cases (.bound 3) (fun i => .bound ⟨i.val+7, by omega⟩)
  let χ : BinarySchema (n+5) := {
    body := .disj
      (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
        (force_at_m φ.body es (.bound 6) (.bound 5) (.bound 4) .newest))
      (.conj (Formula.extensionalEq (.bound 1) (.bound 2))
        (force_at_m (.neg φ.body) es (.bound 6) (.bound 5) (.bound 4) .newest))
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      refine ⟨⟨by simp -implicitDefEqProofs, ?_⟩, by simp -implicitDefEqProofs, ?_⟩
      · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
      · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl }
  have hχ a p : χ.denote δ a p ↔
      (a = s ∧ Forces_d M B R z φ.body (η.push s) p) ∨
      (a = t ∧ Forces_d M B R z (.neg φ.body) (η.push s) p) := by
    have he : (⟨fun i => (es i).eval ((δ.push a).push p), ((δ.push a).push p).free⟩ : Env M (n+1)) = η.push s := by
      apply congrArg (fun f => (⟨f, fun _ => s⟩ : Env M (n+1)))
      exact funext (Fin.cases rfl (fun _ => rfl))
    simp only [BinarySchema.denote, χ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, force_at_sat_l, he]
    rfl
  have clash p q r (hp : M.mem p B) (hrp : Below_d M B R z r p) (hrq : Below_d M B R z r q)
      (yes : Forces_d M B R z φ.body (η.push s) p)
      (no : Forces_d M B R z (.neg φ.body) (η.push s) q) : False :=
    (forces_neg_l hZF.1 _ _ q).mp no r hrq ((reg s hs).1 p r hp hrp yes)
  obtain ⟨a, ha, mix⟩ := name_pool_mix_l O hZF pool χ δ (by
    intro p q a b r hp hq _ _ hpa hqb hrp hrq
    rcases (hχ a p).mp hpa with ⟨ha, yes⟩ | ⟨ha, no⟩
    · rcases (hχ b q).mp hqb with ⟨hb, _⟩ | ⟨_, no⟩
      · rw [ha, hb]; exact eq_force_refl_l O hZF hrp.1 (hn s hs)
      · exact (clash p q r hp hrp hrq yes no).elim
    · rcases (hχ b q).mp hqb with ⟨_, yes⟩ | ⟨hb, _⟩
      · exact (clash q p r hq hrq hrp yes no).elim
      · rw [ha, hb]; exact eq_force_refl_l O hZF hrp.1 (hn t ht))
  have same p hp hf : Eq_force_d M B R z p a s := mix p s hp hs ((hχ s p).mpr (Or.inl ⟨rfl, hf⟩))
  refine ⟨a, ha, ?_, fun p hp hf => same p hp ((change_env s p).mp hf)⟩
  intro p hp hz
  apply (change_env a p).mpr
  apply (reg a ha).2 p hp hz
  intro q hq
  by_cases yes : Forces_d M B R z φ.body (η.push s) q
  · exact ⟨q, below_refl_l O hq.1 hq.2.1,
      (forces_name_congr_l O hZF φ η hρ (hn a ha) (hn s hs) hq.1 hq.2.1 (same q hq.1 yes)).mpr yes⟩
  · obtain ⟨r, hr, no⟩ := regular_neg_witness_l (reg s hs) hq.1 hq.2.1 yes
    have eq := mix r t hr.1 ht ((hχ t r).mpr (Or.inr ⟨rfl, (forces_neg_l hZF.1 _ _ r).mpr no⟩))
    exact ⟨r, hr, (forces_name_congr_l O hZF φ η hρ (hn a ha) (hn t ht) hr.1 hr.2.1 eq).mpr
      ((change_env t r).mp (fallback r hr.1 hr.2.1))⟩

end YesMetaZFC.Model.Forcing.Internal
