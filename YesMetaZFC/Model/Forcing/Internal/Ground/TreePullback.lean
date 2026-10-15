import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.SetTheory.Descriptive.TreePullback

/-! # 树的字母逆像与规范地模型嵌入交换

有限节点和字母映射的图边均有地来源；复合图的唯一性排除新增逆像节点。
无限分支仍在目标模型中重新量化，不假定两模型具有相同分支。
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

theorem image_fseq_recode_l {f X Y n p q : M.Domain} (ff : M.IsSetFunctionFromTo I f X Y)
    (fp : M.IsSetFunctionFromTo I p n X) (h : Fseq_recode_d I f p q) : Fseq_recode_d J (e f) (e p) (e q) := by
  have fq := h.function_l I hM ff fp
  have fq' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fq
  refine ⟨fq'.1.1, fun i y => ?_⟩
  constructor
  · intro iy
    obtain ⟨j, z, jz, rfl, rfl⟩ := (image_entries_l e he fq.1.1 i y).mp iy
    obtain ⟨x, jx, xz⟩ := (h.2 j z).mp jz
    exact ⟨e x, (image_entries_l e he fp.1.1 (e j) (e x)).mpr ⟨j, x, jx, rfl, rfl⟩,
      (image_entries_l e he ff.1.1 (e x) (e z)).mpr ⟨x, z, xz, rfl, rfl⟩⟩
  · rintro ⟨x, ix, xy⟩
    obtain ⟨j, a, ja, rfl, rfl⟩ := (image_entries_l e he fp.1.1 i x).mp ix
    obtain ⟨b, z, bz, eq, rfl⟩ := (image_entries_l e he ff.1.1 (e a) y).mp xy
    have eq := hi eq; subst b
    exact (image_entries_l e he fq.1.1 (e j) (e z)).mpr ⟨j, z, (h.2 j z).mpr ⟨a, ja, bz⟩, rfl, rfl⟩

theorem image_tree_pullback_l {ω X Y f F T S : M.Domain} (ff : M.IsSetFunctionFromTo I f X Y)
    (space : Fseq_space_d I ω X F) (pull : Tr_pull_d I f F T S) : Tr_pull_d J (e f) (e F) (e T) (e S) := by
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (he S p).mp hp
    obtain ⟨hqF, r, hr, qr⟩ := (pull q).mp hq
    obtain ⟨n, _, fq⟩ := (space q).mp hqF
    exact ⟨(image_member_l e hi he).mpr hqF, e r, (image_member_l e hi he).mpr hr,
      image_fseq_recode_l hM hN e hi he ff fq qr⟩
  · rintro ⟨hp, r, hr, pr⟩
    obtain ⟨q, hq, rfl⟩ := (he F p).mp hp
    obtain ⟨s, hs, rfl⟩ := (he T r).mp hr
    obtain ⟨n, _, fq⟩ := (space q).mp hq
    obtain ⟨t, _, qt⟩ := ZF.fseq_compose_l I hM ff fq
    have eq := hi ((image_fseq_recode_l hM hN e hi he ff fq qt).unique_l J hN.1 pr)
    subst t
    exact (image_member_l e hi he).mpr ((pull q).mpr ⟨hq, s, hs, qt⟩)

end YesMetaZFC.Model.Forcing.Internal
