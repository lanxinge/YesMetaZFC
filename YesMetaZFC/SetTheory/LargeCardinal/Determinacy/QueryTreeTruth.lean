import YesMetaZFC.SetTheory.LargeCardinal.Absorption.QueryHull
import YesMetaZFC.Model.Forcing.Order.QueryContext
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection

/-! # 任意正负树分支在真实 L(ℝ) 中给出同一查询点的见证

原联合树的分支自动生成可数传递源和完整泛型。固定三项参数的登记给出
返回原秩层的实际原像，随后原 8.5 上传正负断言，不增加见证正确性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem qs_tree_truth_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R θ u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An Aq x : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (ω A₀ P V σ a₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) ω A₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (fa : Fn0_d ω.val ω.val a₀.val)
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (tree : Qs_tree_d hZF φ sign link.tree σ.val a₀.val Aq)
    (params : Jt_params_d ω.val X P.val V.val C)
    (AC : ∃ i, Rd_entry_d i A₀.val C) (σC : ∃ i, Rd_entry_d i σ.val C) (aC : ∃ i, Rd_entry_d i a₀.val C)
    (projected : Tp_projection_d I ω.val ω.val Yn Fn Aq x) :
    Relative.Lq_signed_d hZF φ sign ω.val a₀.val x := by
  obtain ⟨q',fq',branch',projection⟩ := projected
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  obtain ⟨x',h',t',z',q,u',v',w',N,cN,RN,H,B,π,j,cB,RB,P',V',G,fx,cols,_,_,_,collapse,constants,
      hwB,σ',a',τ',b',p',imageσ,imagea,hb,hp,force,named⟩ := tree.sound_l hZF hc source trans ω P V σ a₀ hw certificate
        (product.order_l native) sh gn joint link params σC aC fq' branch'
  obtain ⟨i,iA⟩ := AC
  obtain ⟨A',imageA,_⟩ := constants i A₀.val iA
  -- 原字母表的查询映射就是第一投影；组成图唯一性固定原对局实数。
  have col : Fseq_recode_d I dx q' x := by
    refine ⟨projection.1.1.1,fun i v => ?_⟩
    constructor
    · intro iv
      obtain ⟨z,t,iz,code⟩ := (projection.2 i v).mp iv
      exact ⟨z,iz,(link.tree.letters.read z v t (fq'.output_mem_of_pairMember iz) code).1⟩
    · rintro ⟨z,iz,zv⟩
      have hz := fq'.output_mem_of_pairMember iz
      obtain ⟨a,_,t,_,code⟩ := (link.tree.letters.product z).mp hz
      have za := (link.tree.letters.read z a t hz code).1
      have eq := link.tree.letters.query.1.2 z v a zv za
      subst a
      exact (projection.2 i v).mpr ⟨z,t,iz,code⟩
  have eq := cols.query.unique_l I hZF.1 col
  subst x'
  exact gh_query_upload_l hZFC hc source trans rank ω A₀ P V σ a₀ hw certificate
    sequence product name fa fx collapse hwB ⟨A',(collapse.collapse.function.bound_l imageA).2⟩ σ' a' τ' b' p'
    imageA imageσ imagea hb hp force named

end YesMetaZFC.SetTheory.LargeCardinal
