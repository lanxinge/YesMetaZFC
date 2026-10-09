import YesMetaZFC.SetTheory.LargeCardinal.IterationUltraRead
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 反射壳中原指定超幂边的回拉

大树的真实超幂证书先由有限反射进入证书层，再沿外层初等图进入小层。
读取原商及塌缩后，Łoś 定理恢复同一张小边的完整证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_pull_l {ω B R b U S u C V π X P K : M.Domain}
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ambient : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C}) (hCV : Rd_entry_d C V π)
    (reflect : Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V)
    (ρ : Env (rt_model_l C nc) 7) (η : Env M 7) (hw : (ρ.bound 6).val = ω)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π)
    (source : Ep_source_d hZF ω (ρ.bound 5).val K X P) (mx : Smem_d I (ρ.bound 2).val X P)
    (family : Em_source_d ω (ρ.bound 5).val (ρ.bound 4).val X (ρ.bound 3).val)
    (coherent : Ec_source_d I ω (ρ.bound 5).val (ρ.bound 4).val X (ρ.bound 3).val)
    (big : It_ultra_d hZF (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0)) :
    It_ultra_d hZF ω (ρ.bound 5).val (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 2).val (ρ.bound 1).val (ρ.bound 0).val := by
  have tr := hj.reflected_l hZF source.omega bt ut mb mu ambient.transitive nc hCV
    (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    (by simp -implicitDefEqProofs) reflect ρ η images
  exact it_ultra_read_l hZFC ambient nc ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    hw source mx family coherent (tr.mpr ((it_ultra_sat_l hZF η ..).mpr big))

end YesMetaZFC.SetTheory.LargeCardinal
