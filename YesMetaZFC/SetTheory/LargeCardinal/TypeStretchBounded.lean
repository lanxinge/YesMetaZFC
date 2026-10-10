import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchCode
import YesMetaZFC.SetTheory.LargeCardinal.TypeStretch

/-! # 有界矩阵与原实际类型伸展的等价

同一扩展器的原超幂提供实际存在性；小关系的坍塌将全部证据放回所属源。
反向读取使用给定坍塌的唯一性，不把低秩像替换成另一个嵌入的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_stretch_d.read_l {ω κ K L X R F c d j N S B t D v : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hB : M.mem B X) (trans : M.TransitiveSet B) (ht : M.mem t B)
    (h : Eb_stretch_d ω κ L K X B F t D v) : Et_stretch_d hZF ω κ L F X R t D v := by
  obtain ⟨A, _, Q, _, Y, _, e, _, y, _, collapse, value, cut⟩ := h
  have image := ((collapse.image_l hZF source family hm hn ultra hB trans).2 t y ht).mp value
  exact ⟨c, d, N, S, j, y, hm, hn, ultra, image, cut⟩

theorem Et_stretch_d.bounded_l {ω κ K L X R F V B t D v : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X) (hl : M.IsLimitOrdinal L) (level : Er_level_d X L V)
    (hκ : M.mem κ V) (hB : M.mem B V) (trans : M.TransitiveSet B) (ht : M.mem t B)
    (h : Et_stretch_d hZF ω κ L F X R t D v) : Eb_stretch_d ω κ L K X B F t D v := by
  have hBX := source.transitive V level.member B hB
  obtain ⟨c, d, N, S, j, y, hm, hn, ultra, image, cut⟩ := h
  obtain ⟨B', _, hBB⟩ := (ultra.elementary_l hZF hm.1 hn.1).1.1.2.2 B hBX
  obtain ⟨hB', A, Q, e, collapse⟩ := it_ultra_owned_image_l hZF source power family hm hn ultra
    hL hF hl level hκ hB trans hBB
  have value := ((collapse.image_l hZF source family hm hn ultra hBX trans).2 t y ht).mpr image
  have owned : M.mem A X ∧ M.mem Q X ∧ M.mem e X ∧ M.mem y X := by
    obtain ⟨_, _, _, _, _, pool, _, _, _, hQ, he, _, _, _, _, map, _⟩ := collapse
    obtain ⟨u, _, _, _, _, _, _, _, _, _, _, huy⟩ := value
    exact ⟨pool.carrier, hQ, he, source.transitive B' hB' y (map.function.bound_l huy).2⟩
  exact ⟨A, owned.1, Q, owned.2.1, B', hB', e, owned.2.2.1, y, owned.2.2.2, collapse, value, cut⟩

end YesMetaZFC.SetTheory.LargeCardinal
