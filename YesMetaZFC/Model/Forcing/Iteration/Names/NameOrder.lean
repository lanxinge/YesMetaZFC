import YesMetaZFC.Model.Forcing.Iteration.Names.Selection
import YesMetaZFC.Model.Forcing.Iteration.Names.Witness

/-! # 商条件名称以下的后继尾部

在每个决定旧条件的分支上比较第二坐标，正是前缀泛型下的商序比较。
该原公式既能进入内部递归，也能直接恢复实际旧条件间的加强关系。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_below_name_d (α B R b t D N T τ p s : M.Domain) : Prop :=
  ∀ u a, Row_pick_d (M := M) α B R b t D N τ u a → Below_d M B R B a p →
    Rel_force_d M B R B T a s u

def row_below_name_m {n} (α B R b t D N T τ p s : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (row_pick_m α.weaken.weaken B.weaken.weaken R.weaken.weaken
    b.weaken.weaken t.weaken.weaken D.weaken.weaken N.weaken.weaken τ.weaken.weaken (.bound 1) .newest)
    (.imp (below_m B.weaken.weaken R.weaken.weaken B.weaken.weaken .newest p.weaken.weaken)
      (rel_force_m B.weaken.weaken R.weaken.weaken B.weaken.weaken T.weaken.weaken .newest s.weaken.weaken (.bound 1)))))
derive_free_closed row_below_name_m

theorem row_below_name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R b t D N T τ p s : Term n) :
    Formula.satisfies ρ (row_below_name_m α B R b t D N T τ p s) ↔
      Row_below_name_d (M := M) (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (t.eval ρ)
        (D.eval ρ) (N.eval ρ) (T.eval ρ) (τ.eval ρ) (p.eval ρ) (s.eval ρ) := by
  simp only [row_below_name_m, Row_below_name_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    row_pick_sat_l hE, below_sat_l M hE, rel_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 对混合坐标的加强，在每个旧条件决定分支上也是加强。 -/
theorem row_select_below_l (hZF : M.Models ZF) {α B R b A T t W C S D V N τ p u s}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (k : Row_repr_d M α t C S D V) (hT : Name_d M B T) (hu : Name_d M B u) (hs : Name_d M B s)
    (hp : M.mem p B) (hle : Rel_force_d M B R B T p s u)
    (hsel : ∀ v a, Row_pick_d (M := M) α B R b t D N τ v a → Eq_force_d M B R B a u v) :
    Row_below_name_d (M := M) α B R b t D N T τ p s := by
  intro v a hv hap
  have he := hsel v a hv
  obtain ⟨r, c, _, hr, _, hc, hcr, _⟩ := hv
  have hvN : Name_d M B v := ⟨W, (row_repr_decode_l hZF h hStep k hr hc hcr).1, hStep.closed⟩
  let ρ := ord_env_l M s T
  let φ : UnarySchema 2 := { body := rel_at_m (.bound 1) .newest (.bound 2) }
  have hf := (forces_name_congr_l h.order hZF φ ρ (Fin.cases hs (fun _ => hT)) hu hvN hap.1 hap.2.1 he).mp
    ((force_rel_at_l M hZF.1 (ρ.push u) a (.bound 1) .newest (.bound 2)).mpr
      ((rel_force_regular_l h.order hZF hT hs hu).1 p a hp hap hle))
  exact (force_rel_at_l M hZF.1 (ρ.push v) a (.bound 1) .newest (.bound 2)).mp hf

/-- 旧条件已被决定且其前缀高于 p 时，商序比较恢复真正的整条条件加强。 -/
theorem row_below_name_ground_l (hZF : M.Models ZF) {α B R b A T t W C S D V N τ p s q r a u v}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (k : Row_repr_d M α t C S D V) (hq : M.mem q D) (hp : M.mem p B)
    (hpq : Row_append_d M α t p s q) (hr : M.mem r D) (hrN : M.mem r N)
    (ha : M.mem a B) (har : Row_append_d M α t a u r) (hpa : Entry_d M p a R)
    (hv : Check_d M b r v) (he : Eq_force_d M B R B p τ v)
    (hl : Row_below_name_d (M := M) α B R b t D N T τ p s) : Entry_d M q r V := by
  have hpz : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  have hsu := hl u p ⟨r, a, v, hr, hrN, ha, har, hv, ⟨hp, hpz, hpa⟩, he⟩ (below_refl_l h.order hp hpz)
  obtain ⟨_, _, x, hx, hxp⟩ := row_repr_decode_l hZF h hStep k hq hp hpq
  obtain ⟨_, _, y, hy, hya⟩ := row_repr_decode_l hZF h hStep k hr ha har
  exact (k.relation q r).mpr ⟨x, y, hx, hy, ⟨p, s, hxp, hpq⟩, ⟨a, u, hya, har⟩,
    (two_step_le_l hStep hx hy hxp hya).mpr ⟨⟨hp, hpz, hpa⟩, hsu⟩⟩

end YesMetaZFC.Model.Forcing.Internal
