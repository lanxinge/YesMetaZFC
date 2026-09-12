import YesMetaZFC.Model.Boolean.Algebra

/-! # 布尔条件下的逻辑同余

同一条件控制两个真值的双向蕴含。有限联结词只需要布尔代数，
量词对应的上、下确界同余另消费完备性。
-/

namespace YesMetaZFC.Model.Boolean
universe u v
namespace BA_alg
variable {B : Type u} (𝔹 : BA_alg B)

def Agree (c a b : B) : Prop := 𝔹.le (𝔹.meet c a) b ∧ 𝔹.le (𝔹.meet c b) a

theorem agree_refl (c a : B) : 𝔹.Agree c a a := ⟨𝔹.meet_le_right _ _, 𝔹.meet_le_right _ _⟩

theorem agree_cut {c a b : B} (h : 𝔹.Agree c a b) : 𝔹.meet c a = 𝔹.meet c b :=
  𝔹.le_antisymm (𝔹.le_meet (𝔹.meet_le_left _ _) h.1) (𝔹.le_meet (𝔹.meet_le_left _ _) h.2)

theorem agree_mono {c d a b : B} (h : 𝔹.le c d) (k : 𝔹.Agree d a b) : 𝔹.Agree c a b :=
  ⟨𝔹.le_trans (𝔹.meet_mono h (𝔹.le_refl _)) k.1, 𝔹.le_trans (𝔹.meet_mono h (𝔹.le_refl _)) k.2⟩

theorem imp_under {c a a' b b' : B}
    (h : 𝔹.le (𝔹.meet c a') a) (k : 𝔹.le (𝔹.meet c b) b') :
    𝔹.le (𝔹.meet c (𝔹.imp a b)) (𝔹.imp a' b') := by
  apply (𝔹.le_imp_iff _ _ _).mpr
  have hc : 𝔹.le (𝔹.meet (𝔹.meet c (𝔹.imp a b)) a') c :=
    𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)
  have ha := 𝔹.le_trans (𝔹.le_meet hc (𝔹.meet_le_right _ _)) h
  exact 𝔹.le_trans (𝔹.le_meet hc
    (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) ha)) k

theorem agree_imp {c a a' b b' : B} (h : 𝔹.Agree c a a') (k : 𝔹.Agree c b b') :
    𝔹.Agree c (𝔹.imp a b) (𝔹.imp a' b') := ⟨𝔹.imp_under h.2 k.1, 𝔹.imp_under h.1 k.2⟩

theorem agree_neg {c a a' : B} (h : 𝔹.Agree c a a') : 𝔹.Agree c (𝔹.neg a) (𝔹.neg a') :=
  𝔹.agree_imp h (𝔹.agree_refl c 𝔹.bot)

theorem agree_meet {c a a' b b' : B} (h : 𝔹.Agree c a a') (k : 𝔹.Agree c b b') :
    𝔹.Agree c (𝔹.meet a b) (𝔹.meet a' b') := ⟨
  𝔹.le_meet (𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.meet_le_left _ _)) h.1)
    (𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.meet_le_right _ _)) k.1),
  𝔹.le_meet (𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.meet_le_left _ _)) h.2)
    (𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.meet_le_right _ _)) k.2)⟩

theorem agree_join {c a a' b b' : B} (h : 𝔹.Agree c a a') (k : 𝔹.Agree c b b') :
    𝔹.Agree c (𝔹.join a b) (𝔹.join a' b') :=
  𝔹.agree_neg (𝔹.agree_meet (𝔹.agree_neg h) (𝔹.agree_neg k))

theorem agree_iff {c a a' b b' : B} (h : 𝔹.Agree c a a') (k : 𝔹.Agree c b b') :
    𝔹.Agree c (𝔹.iff a b) (𝔹.iff a' b') := 𝔹.agree_meet (𝔹.agree_imp h k) (𝔹.agree_imp k h)

end BA_alg
namespace CB_alg
variable {B : Type u} (𝔹 : CB_alg B)

theorem agree_iSup {ι : Sort v} {c : B} {f g : ι → B} (h : ∀ i, 𝔹.Agree c (f i) (g i)) :
    𝔹.Agree c (𝔹.iSup f) (𝔹.iSup g) := by
  constructor
  · rw [𝔹.meet_iSup]
    exact (𝔹.iSup_le_iff _ _).mpr (fun i => 𝔹.le_trans (h i).1 (𝔹.le_iSup g i))
  · rw [𝔹.meet_iSup]
    exact (𝔹.iSup_le_iff _ _).mpr (fun i => 𝔹.le_trans (h i).2 (𝔹.le_iSup f i))

theorem agree_iInf {ι : Sort v} {c : B} {f g : ι → B} (h : ∀ i, 𝔹.Agree c (f i) (g i)) :
    𝔹.Agree c (𝔹.iInf f) (𝔹.iInf g) := ⟨
  (𝔹.le_iInf_iff _ _).mpr (fun i => 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.iInf_le f i)) (h i).1),
  (𝔹.le_iInf_iff _ _).mpr (fun i => 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (𝔹.iInf_le g i)) (h i).2)⟩

end CB_alg
end YesMetaZFC.Model.Boolean
