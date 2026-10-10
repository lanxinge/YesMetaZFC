import YesMetaZFC.Model.Forcing.Closed.Name
import YesMetaZFC.Model.Forcing.TwoStep.Witness
import YesMetaZFC.SetTheory.FunctionCoordinates

/-! # 可数闭二步迭代及固定首坐标的下界

投影实际下降链，先固定压住全部首坐标的 p。第二坐标在 p 下组成名称链；
后继闭性与最大值原理给出统一下界，再装回原混合闭名称库，精确保留 p。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T a W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 任意下降链的给定共同首前缀，原样提升为整条二步链的下界。 -/
theorem two_step_chain_bound_l (h : Two_step_d M B R z b A T W C S)
    (hW : Name_pool_d M B A a W) (hT : Name_d M B T) (L : Cond_order_d M C S C)
    {ω w f p} (hω : M.IsOmega ω) (hw : Check_d M b ω w) (hf : Chain_d I C S C ω f)
    (hp : Below_d M B R z p b)
    (hpf : ∀ i x q s, Entry_d M i x f → KPair_d M x q s → Entry_d M p q R)
    (hc : Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p) :
    ∃ y s, M.mem y C ∧ KPair_d M y p s ∧ ∀ i x, Entry_d M i x f → Entry_d M y x S := by
  have coords c (hc : M.mem c C) : ∃ q s, M.mem q B ∧ M.mem s W ∧ KPair_d M c q s := by
    obtain ⟨q, s, hqs, hs, hq, _⟩ := (h.conditions c).mp hc
    exact ⟨q, s, hq.1, hs, hqs⟩
  obtain ⟨G, H, _, hH, hcoords⟩ := ZF.function_coords_l I hZF hf.1 coords
  have part {i s} (his : Entry_d M i s H) : ∃ x q, Entry_d M i x f ∧ KPair_d M x q s := by
    obtain ⟨x, hx, hix⟩ := hf.1.2.2 i (hH.input_mem_of_pairMember his)
    obtain ⟨q, t, hxt, _⟩ := (h.conditions x).mp hx
    have he := hH.1.2 i t s (hcoords i x q t hix hxt).2 his
    exact ⟨x, q, hix, he ▸ hxt⟩
  have hn s (hs : M.mem s W) : Name_d M B s := ⟨W, hs, h.closed⟩
  have hA : Name_d M B A := hn A h.root
  have hChain : Nchain_d I B R z p ω A T H := by
    refine ⟨hH.1, hH.2.1, fun i s his => ?_, fun i j s t hij his hjt => ?_⟩
    · obtain ⟨x, q, hix, hxq⟩ := part his
      obtain ⟨hs, hq, hqs⟩ := (two_step_mem_l h hxq).mp (hf.1.output_mem_of_pairMember hix)
      exact ⟨hn s hs, (regular_mem_l O s A).1 q p hq.1 ⟨hp.1, hp.2.1, hpf i x q s hix hxq⟩ hqs⟩
    · obtain ⟨x, q, hix, hxq⟩ := part his
      obtain ⟨y, r, hjy, hyr⟩ := part hjt
      have hx := hf.1.output_mem_of_pairMember hix
      have hy := hf.1.output_mem_of_pairMember hjy
      have hs := (two_step_mem_l h hxq).mp hx
      have ht := (two_step_mem_l h hyr).mp hy
      have hts := ((two_step_le_l h hy hx hyr hxq).mp (chain_lower_l L hZF hω hf i j x y hij hix hjy)).2
      exact (rel_force_regular_l O hZF hT (hn t ht.1) (hn s hs.1)).1 r p ht.2.1.1
        ⟨hp.1, hp.2.1, hpf j y r t hjy hyr⟩ hts
  obtain ⟨t, ht⟩ := nseq_exists_l M hZF h.base hH (fun _ s his => hn s (hH.output_mem_of_pairMember his))
  obtain ⟨v, hv, hvA, hvH⟩ := nchain_bound_name_l O hZFC h.base hp hChain ht hw hA hT hc
  obtain ⟨s, y, hs, hyp, hy, hsv⟩ := two_step_represent_l O hZF h hW hv hp hvA
  refine ⟨y, s, hy, hyp, fun i x hix => ?_⟩
  have hx := hf.1.output_mem_of_pairMember hix
  obtain ⟨q, t, hxq, ht, _, _⟩ := (h.conditions x).mp hx
  have hst := (rel_force_congr_l O hZF hT (hn s hs) (hn t ht) hv (hn t ht) hp.1 hp.2.1
    hsv (eq_force_refl_l O hZF hp.1 (hn t ht))).mpr (hvH i t (hcoords i x q t hix hxq).2)
  exact (two_step_le_l h hy hx hyp hxq).mpr ⟨⟨hp.1, hp.2.1, hpf i x q t hix hxq⟩, hst⟩

/-- 首阶段可数闭且迫使后继可数闭，则实际混合闭库二步偏序可数闭。 -/
theorem two_step_closed_l (h : Two_step_d M B R z b A T W C S)
    (hW : Name_pool_d M B A a W) (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) b)
    {ω w} (hω : M.IsOmega ω) (hw : Check_d M b ω w) (hB : Closed_d I B R z ω)
    (hc : Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) b) : Closed_d I C S C ω := by
  intro f hf
  have L := two_step_order_l O hZF h hT hP
  obtain ⟨G, H, hG, _, hcoords⟩ := ZF.function_coords_l I hZF hf.1 (fun c hc => by
    obtain ⟨q, s, hcs, hs, hq, _⟩ := (h.conditions c).mp hc
    exact ⟨q, s, hq.1, hs, hcs⟩)
  have part {i q} (hiq : Entry_d M i q G) : ∃ x s, Entry_d M i x f ∧ KPair_d M x q s := by
    obtain ⟨x, hx, hix⟩ := hf.1.2.2 i (hG.input_mem_of_pairMember hiq)
    obtain ⟨r, s, hxs, _⟩ := (h.conditions x).mp hx
    have he := hG.1.2 i r q (hcoords i x r s hix hxs).1 hiq
    exact ⟨x, s, hix, he ▸ hxs⟩
  have hchain : Chain_d I B R z ω G := by
    refine ⟨hG, fun i q hiq => ?_, fun i j q r hij hiq hjr => ?_⟩
    · obtain ⟨x, s, hix, hxs⟩ := part hiq
      exact ((two_step_mem_l h hxs).mp (hf.1.output_mem_of_pairMember hix)).2.1.2.1
    · obtain ⟨x, s, hix, hxs⟩ := part hiq
      obtain ⟨y, t, hjy, hyt⟩ := part hjr
      exact ((two_step_le_l h (hf.1.output_mem_of_pairMember hjy) (hf.1.output_mem_of_pairMember hix)
        hyt hxs).mp (hf.2.2 i j x y hij hix hjy)).1.2.2
  obtain ⟨p, hp, hpz, hpg⟩ := hB G hchain
  obtain ⟨o, _, hoω⟩ := hω.1.1
  obtain ⟨q, hq, hoq⟩ := hG.2.2 o hoω
  obtain ⟨x, s, hox, hxs⟩ := part hoq
  have hqb := ((two_step_mem_l h hxs).mp (hf.1.output_mem_of_pairMember hox)).2.1.2.2
  have hpb : Below_d M B R z p b := ⟨hp, hpz, O.trans p q b hp hq h.base (hpg o q hoq) hqb⟩
  have hwN := check_name_l M (check_range_l M hZF) h.base hw
  have hA : Name_d M B A := ⟨W, h.root, h.closed⟩
  have hn : ∀ t : Term 3, Name_d M B
      (t.eval (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T)) := by
    intro t
    cases t with
    | free _ => exact hwN
    | bound i => exact Fin.cases hT (Fin.cases hA (fun _ => hwN)) i
  have hcp := (forces_regular_l O hZF _ _ hn).1 b p h.base hpb hc
  obtain ⟨y, s, hy, _, hyf⟩ := two_step_chain_bound_l O hZFC h hW hT L hω hw hf hpb
    (fun i x q s hix hxs => hpg i q (hcoords i x q s hix hxs).1) hcp
  exact ⟨y, hy, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hy), hyf⟩

end YesMetaZFC.Model.Forcing.Internal
