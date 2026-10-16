import YesMetaZFC.Model.Forcing.Internal.Ground.Arithmetic
import YesMetaZFC.SetTheory.Descriptive.HistoryTree

/-! # 旧历史的策略服从性与截面条件保持

目标中的限制图由源中的实际限制图唯一确定。因此有限历史的策略控制条件
逐项绝对，证明不假定策略在目标中仍获胜。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem image_follows_l {b : Bool} {ω K σ f : M.Domain} (rel : M.IsSetRelation I f) :
    Cg_follows_d J b (e ω) (e K) (e σ) (e f) ↔ Cg_follows_d I b ω K σ f := by
  have turn i : (if b then N.mem (e i) (e K) else ¬ N.mem (e i) (e K)) ↔
      (if b then M.mem i K else ¬ M.mem i K) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, image_member_l e hi he]
  constructor
  · intro follows i hin own h cut a value
    exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 h a σ).mpr
      (follows (e i) ((image_member_l e hi he).mpr hin) ((turn i).mpr own) (e h)
        (image_restriction_l hM hN e hi he rel cut) (e a)
        ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i a f).mp value))
  · intro follows i hin own h cut a value
    obtain ⟨k, hk, rfl⟩ := (he ω i).mp hin
    obtain ⟨g, cut'⟩ := ZF.exists_restriction hM I f k
    have eq := cut.eq hN.1 (image_restriction_l hM hN e hi he rel cut')
    subst h
    obtain ⟨l, z, lz, eq, rfl⟩ := (image_entries_l e he rel (e k) a).mp value
    have eq := hi eq; subst l
    exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 g z σ).mp
      (follows k hk ((turn k).mp own) g cut' z lz)

theorem image_hg_strategy_l {b : Bool} {ω X F K σ S : M.Domain}
    (space : Fseq_space_d I ω X F)
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ Cg_follows_d I b ω K σ s) :
    ∀ s, N.mem s (e S) ↔ N.mem s (e F) ∧ Cg_follows_d J b (e ω) (e K) (e σ) s := by
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he S s).mp hs
    obtain ⟨hf, follows⟩ := (read t).mp ht
    obtain ⟨_, _, ft⟩ := (space t).mp hf
    exact ⟨(image_member_l e hi he).mpr hf, (image_follows_l hM hN e hi he ft.1.1).mpr follows⟩
  · rintro ⟨hs, follows⟩
    obtain ⟨t, ht, rfl⟩ := (he F s).mp hs
    obtain ⟨_, _, ft⟩ := (space t).mp ht
    exact (image_member_l e hi he).mpr ((read t).mpr
      ⟨ht, (image_follows_l hM hN e hi he ft.1.1).mp follows⟩)

theorem image_hg_section_l {F x S : M.Domain}
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ M.MemberSubset s x) :
    ∀ s, N.mem s (e S) ↔ N.mem s (e F) ∧ N.MemberSubset s (e x) := by
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he S s).mp hs
    exact ⟨(image_member_l e hi he).mpr ((read t).mp ht).1,
      (image_subset_iff_l e hi he).mpr ((read t).mp ht).2⟩
  · rintro ⟨hs, sub⟩
    obtain ⟨t, ht, rfl⟩ := (he F s).mp hs
    exact (image_member_l e hi he).mpr ((read t).mpr ⟨ht, (image_subset_iff_l e hi he).mp sub⟩)

end YesMetaZFC.Model.Forcing.Internal
