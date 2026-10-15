import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.SetTheory.Descriptive.TreeShift

/-! # 首项拼接和移位树沿地嵌入保持

只传递地有限节点的图方程。扩张中的全部无限分支另由目标模型内部的移位定理处理。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_cons_l {z a s t : M.Domain} (fs : M.IsSetRelation I s) (h : Cons_d I z a s t) :
    Cons_d J (e z) (e a) (e s) (e t) := by
  refine ⟨?_, fun j x => ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := (he t q).mp hq
    obtain ⟨i, v, c⟩ := h.1 p hp
    exact ⟨e i, e v, image_kpair_l e he c⟩
  · constructor
    · intro jx
      obtain ⟨i, y, iy, rfl, rfl⟩ := (image_entries_l e he h.1 j x).mp jx
      rcases (h.2 i y).mp iy with ⟨rfl, rfl⟩ | ⟨k, ky, sk⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨e k, (image_entries_l e he fs (e k) (e y)).mpr ⟨k, y, ky, rfl, rfl⟩,
          image_successor_l (hEN := hN.1) e hi he hM.1 sk⟩
    · rintro (⟨rfl, rfl⟩ | ⟨i, ix, sj⟩)
      · exact (image_entries_l e he h.1 (e z) (e a)).mpr ⟨z, a, (h.2 z a).mpr (Or.inl ⟨rfl, rfl⟩), rfl, rfl⟩
      · obtain ⟨k, y, ky, rfl, rfl⟩ := (image_entries_l e he fs i x).mp ix
        obtain ⟨l, sl⟩ := KP.exists_successor (ZF.modelsKP hM) k
        have eq := (image_successor_l (hEN := hN.1) e hi he hM.1 sl).eq hN.1 sj
        exact eq ▸ (image_entries_l e he h.1 (e l) (e y)).mpr ⟨l, y, (h.2 l y).mpr (Or.inr ⟨k, ky, sl⟩), rfl, rfl⟩

theorem image_tree_shift_l {ω X z F T S : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (hz : ∀ x, ¬ M.mem x z) (space : Fseq_space_d I ω X F) (subT : M.MemberSubset T F)
    (shift : Tr_shift_d I z F T S) : Tr_shift_d J (e z) (e F) (e T) (e S) := by
  have hz' y (hy : N.mem y (e z)) : False := (he z y).mp hy |>.elim fun x hx => hz x hx.1
  intro t
  constructor
  · intro ht
    obtain ⟨q, hq, rfl⟩ := (he S t).mp ht
    obtain ⟨hqF, tail⟩ := (shift q).mp hq
    refine ⟨(image_member_l e hi he).mpr hqF, ?_⟩
    rcases tail with rfl | ⟨a, s, hs, cs⟩
    · exact Or.inl rfl
    · obtain ⟨_, _, fs⟩ := (space s).mp (subT s hs)
      exact Or.inr ⟨e a, e s, (image_member_l e hi he).mpr hs, image_cons_l hM hN e hi he fs.1.1 cs⟩
  · rintro ⟨ht, tail⟩
    obtain ⟨q, hq, rfl⟩ := (he F t).mp ht
    apply (image_member_l e hi he).mpr
    refine (shift q).mpr ⟨hq, ?_⟩
    rcases cons_cases_l I hM hw space hz hq with eq | ⟨a, s, _, hs, cs⟩
    · exact Or.inl eq
    · rcases tail with eq | ⟨b, r, hr, cr⟩
      · exact (cons_ne_empty_l I hz cs (hi eq)).elim
      · obtain ⟨t, ht, rfl⟩ := (he T r).mp hr
        obtain ⟨n, hn, fs⟩ := (space s).mp hs
        obtain ⟨m, hm, ft⟩ := (space t).mp (subT t ht)
        have eq := (cons_injective_l J hN hw' hz' ((image_member_l e hi he).mpr hn) ((image_member_l e hi he).mpr hm)
          (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs)
          (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he ft)
          (image_cons_l hM hN e hi he fs.1.1 cs) cr).2
        exact Or.inr ⟨a, s, (hi eq).symm ▸ ht, cs⟩

end YesMetaZFC.Model.Forcing.Internal
