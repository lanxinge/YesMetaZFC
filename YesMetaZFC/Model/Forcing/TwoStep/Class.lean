import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 全部条件名称上的二步序

先在可定义的名称条件类上证明自反性与传递性，再限制到实际闭名称库。
迭代递归得到的名称族也可直接使用同一序，避免要求它们预先属于某个固定库。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Step_le_d (B R z T x y : M.Domain) : Prop :=
  ∃ p s q t, KPair_d M x p s ∧ KPair_d M y q t ∧ Below_d M B R z p q ∧ Rel_force_d M B R z T p s t

def step_le_m {n} (B R z T x y : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m x.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.conj (kpair_m y.weaken.weaken.weaken.weaken (.bound 1) .newest)
        (.conj (below_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
          z.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (rel_force_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            z.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)))))))
derive_free_closed step_le_m

theorem step_le_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z T x y : Term n) :
    Formula.satisfies ρ (step_le_m B R z T x y) ↔
      Step_le_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (T.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [step_le_m, Step_le_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, below_sat_l M hE, rel_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Step_named_d (B R z b A x : M.Domain) : Prop :=
  ∃ p s, KPair_d M x p s ∧ Name_d M B s ∧ Below_d M B R z p b ∧ Mem_force_d M B R z p s A

def step_named_m {n} (B R z b A x : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m x.weaken.weaken (.bound 1) .newest)
    (.conj (name_m B.weaken.weaken .newest)
      (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) b.weaken.weaken)
        (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) .newest A.weaken.weaken)))))
derive_free_closed step_named_m

theorem step_named_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b A x : Term n) :
    Formula.satisfies ρ (step_named_m B R z b A x) ↔
      Step_named_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (A.eval ρ) (x.eval ρ) := by
  simp only [step_named_m, Step_named_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, name_sat_l M hE, below_sat_l M hE, mem_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

variable {M} {B R z b A T : M.Domain}

theorem step_le_iff_l {x y p s q t} (hx : KPair_d M x p s) (hy : KPair_d M y q t) :
    Step_le_d M B R z T x y ↔ Below_d M B R z p q ∧ Rel_force_d M B R z T p s t := by
  constructor
  · rintro ⟨p', s', q', t', hx', hy', h⟩
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hx hx'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hy hy'
    exact h
  · exact fun h => ⟨p, s, q, t, hx, hy, h⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
  (hA : Name_d M B A) (hT : Name_d M B T) (hb : M.mem b B)
  (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
include O hZF hA hT hb hP

private theorem named_preord_l {p} (hp : Below_d M B R z p b) :
    Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) p := by
  apply (forces_regular_l O hZF _ _ ?_).1 b p hb hp hP
  intro t
  cases t with
  | free _ => exact hT
  | bound i => exact Fin.cases hA (fun _ => hT) i

theorem step_named_refl_l {x} (hx : Step_named_d M B R z b A x) : Step_le_d M B R z T x x := by
  obtain ⟨p, s, hx, hs, hp, hm⟩ := hx
  exact (step_le_iff_l hx hx).mpr ⟨below_refl_l O hp.1 hp.2.1,
    (forced_preord_l O hZF hA hT hp.1 hp.2.1 (named_preord_l O hZF hA hT hb hP hp)).1 s hs hm⟩

theorem step_named_trans_l {x y z'} (hx : Step_named_d M B R z b A x)
    (hy : Step_named_d M B R z b A y) (hz : Step_named_d M B R z b A z')
    (hxy : Step_le_d M B R z T x y) (hyz : Step_le_d M B R z T y z') : Step_le_d M B R z T x z' := by
  obtain ⟨p, s, hx, hs, hpb, hsm⟩ := hx
  obtain ⟨q, t, hy, ht, hqb, htm⟩ := hy
  obtain ⟨r, v, hz, hv, hrb, hvm⟩ := hz
  obtain ⟨hpq, hst⟩ := (step_le_iff_l hx hy).mp hxy
  obtain ⟨hqr, htv⟩ := (step_le_iff_l hy hz).mp hyz
  have hpr := below_trans_l O hrb.1 hpq hqr
  refine (step_le_iff_l hx hz).mpr ⟨hpr, ?_⟩
  exact (forced_preord_l O hZF hA hT hpb.1 hpb.2.1 (named_preord_l O hZF hA hT hb hP hpb)).2
    s t v hs ht hv hsm ((regular_mem_l O t A).1 q p hqb.1 hpq htm)
    ((regular_mem_l O v A).1 r p hrb.1 hpr hvm) hst
    ((rel_force_regular_l O hZF hT ht hv).1 q p hqb.1 hpq htv)

end YesMetaZFC.Model.Forcing.Internal
