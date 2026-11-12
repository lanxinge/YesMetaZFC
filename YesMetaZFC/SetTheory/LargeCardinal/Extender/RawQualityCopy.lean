import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalFormula
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.OwnerQuality

/-! # 原所属模型中的 nice 扩展器在工作源中的实际像

完整初等图搬运原秩段及其有界强度证书。有限列空间也沿同一图搬运，
随后在工作源中读取并沿实际极限秩段向上保持，得到可直接施加的扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原源保持其关系表示；只有目标工作源使用实际隶属关系。 -/
private theorem er_quality_copy_l {Ω c N T d Y S σ z μ H κ L F : M.Domain}
    (mx : Smdl_d I c N T) (my : Smem_d I d Y S) (map : Smap_d I Ω c d N Y σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (w ξ ℓ e V δ K r : (smdl_structure_l I (R := T) mx.2.1).Domain)
    (numbers : Rr_layer_d I Ω N T w.val z)
    (source : Ep_source_d (kp_pair_l hN) w ξ K V r)
    (rank : V_d (kp_pair_l hN) δ V)
    (height : (smdl_structure_l I (R := T) mx.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w V r ξ ℓ e)
    (strong : Ex_strength_d (kp_pair_l hN) w ξ ℓ V e)
    (card : Sc_inaccessible_d w V ℓ) (work : Ep_source_d I Ω μ H Y S)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (he : Rd_entry_d e.val F σ) :
    ∃ K', Ep_source_d I Ω κ K' Y S ∧ It_local_d I Ω Y S κ L F ∧
      Ex_strength_d I Ω κ L Y F ∧ Sc_inaccessible_d Ω Y L := by
  let A := smdl_structure_l I (R := T) mx.2.1
  let B := smdl_structure_l I (R := S) my.1.2.1
  have hB := map.native_models_l hZF work.omega mx my.1 hN
  have ext : Rf_ext_d I N T := fun a ha b hb same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨a, ha⟩ ⟨b, hb⟩ (fun x => same x.val x.property))
  have hw := (numbers.omega_image_mem_l I hZF work.omega ext mx my work.transitive map).1
  let w' : B.Domain := ⟨Ω, work.omega_mem⟩
  let ξ' : B.Domain := ⟨κ, map.1.1.output_mem_of_pairMember hξ⟩
  let ℓ' : B.Domain := ⟨L, map.1.1.output_mem_of_pairMember hℓ⟩
  let e' : B.Domain := ⟨F, map.1.1.output_mem_of_pairMember he⟩
  obtain ⟨H₀, _, sh⟩ := (source.sequences_l hN).1 ℓ strong.2.2.1
  obtain ⟨v, hv, hV⟩ := map.1.1.2.2 V.val V.property
  obtain ⟨a, ha, hδ⟩ := map.1.1.2.2 δ.val δ.property
  obtain ⟨k, hk, hK⟩ := map.1.1.2.2 K.val K.property
  obtain ⟨b, hb, hH⟩ := map.1.1.2.2 H₀.val H₀.property
  let V' : B.Domain := ⟨v, hv⟩
  let δ' : B.Domain := ⟨a, ha⟩
  let K' : B.Domain := ⟨k, hk⟩
  let H' : B.Domain := ⟨b, hb⟩
  have algebra := work.algebra_l (ZF.modelsKP hZF)
  -- 量词覆盖两个原生结构的全部有限列，读回时使用工作源已有的集合代数。
  have seq (a b : A.Domain) (a' b' : B.Domain)
      (haa : Rd_entry_d a.val a'.val σ) (hbb : Rd_entry_d b.val b'.val σ)
      (finite : Fseq_space_d (kp_pair_l hN) w a b) : Fseq_space_d I Ω a'.val b'.val := by
    let ρ : Env A 3 := ⟨Fin.cases b (Fin.cases a (fun _ => w)), fun _ => w⟩
    let η : Env B 3 := ⟨Fin.cases b' (Fin.cases a' (fun _ => w')), fun _ => w'⟩
    have tr := smap_source_l I hZF work.omega mx my.1 map
      (fseq_space_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ η (Fin.cases hbb (Fin.cases haa (fun _ => hw)))
    have native := (fseq_space_sat_l (kp_pair_l hB) hB.1 η (.bound 2) (.bound 1) .newest).mp
      (tr.mp ((fseq_space_sat_l (kp_pair_l hN) hN.1 ρ (.bound 2) (.bound 1) .newest).mpr finite))
    have read := (sc_fseq_native_l I my.1.2.1 hB.1 w' a' b').mpr (fun f => (native f).trans
      (exists_congr fun n => and_congr_right fun _ => ⟨fn0_of_function_l hB, fn0_function_l hB⟩))
    exact (sc_fseq_mem_l I (ZF.modelsKP hZF) work.omega work.transitive my work.omega_mem
      a'.property b'.property algebra.pair algebra.union).mp read
  have sk := seq ξ K ξ' K' hξ hK (source.finite_l hN)
  have sl := seq ℓ H₀ ℓ' H' hℓ hH sh
  have lift {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
      (ρ : Env A n) (η : Env B n)
      (params : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val σ) :
      Formula.satisfies ρ φ → Formula.satisfies (image_env_l (M := B) (N := M) Subtype.val η) φ :=
    fun valid => (smem_delta_image_l I my work.transitive delta η).mp
      ((smap_source_l I hZF work.omega mx my.1 map φ closed ρ η params).mp valid)
  -- 同一个有界公式同时搬运局部扩展器、不可达性和最大强度的实际见证。
  let ρ : Env A 7 := ⟨fun i => [H₀, K, e, V, ℓ, ξ, w].get i, fun _ => w⟩
  let η : Env B 7 := ⟨fun i => [H', K', e', V', ℓ', ξ', w'].get i, fun _ => w'⟩
  let θ : Env M 7 := image_env_l Subtype.val η
  let φ : Formula 1 7 := .conj (ex_local_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
    (.conj (ex_inaccessible_m (.bound 6) (.bound 3) (.bound 4))
      (ex_strength0_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))
  have valid : Formula.satisfies ρ φ := ⟨
    (ex_local_sat_l (kp_pair_l hN) ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      source.transitive source.code).mpr loc,
    (ex_inaccessible_sat_l ρ (.bound 6) (.bound 3) (.bound 4) source.transitive).mpr card,
    (ex_strength0_sat_l hN ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
      (source.finite_l hN) sh).mpr strong⟩
  have moved := lift φ (by exact ⟨by simp -implicitDefEqProofs,
    by simp -implicitDefEqProofs, by simp -implicitDefEqProofs⟩)
    (.conj (ex_local_delta_l ..) (.conj (ex_inaccessible_delta_l ..) (ex_strength0_delta_l ..))) ρ η
    (Fin.cases hH (Fin.cases hK (Fin.cases he (Fin.cases hV (Fin.cases hℓ (Fin.cases hξ
      (Fin.cases hw (fun i => Fin.elim0 i)))))))) valid
  have strength : Ex_strength_d I Ω κ L v F :=
    (ex_strength0_sat_l (ZF.modelsKP hZF) θ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      (.bound 1) .newest sk sl).mp moved.2.2
  -- 原 Vδ 的像只需是工作源中的相对秩段；极限高度由有界公式读回。
  have relative := (rr_rank_mem_l I (ZF.modelsKP hZF) my work.transitive ha hv).mp
    ((rr_rank_truth_l I).mpr (((rr_rank_truth_l I).mp ((rr_rank_native_l I mx.2.1 hN δ V).mpr rank)).map_l
      I hZF work.omega mx my.1 map (by simp -implicitDefEqProofs) (Fin.cases hV (fun _ => hδ))))
  have limit : M.IsLimitOrdinal a := (KP.limit0_sat_l (ZF.modelsKP hZF)
    (image_env_l (M := B) (N := M) Subtype.val (⟨fun _ => δ', fun _ => δ'⟩ : Env B 1)) .newest).mp
      (lift (KP.limit0_m .newest) (by simp -implicitDefEqProofs) (KP.limit0_delta_l ..)
        ⟨fun _ => δ, fun _ => δ⟩ ⟨fun _ => δ', fun _ => δ'⟩ (fun _ => hδ)
        ((KP.limit0_sat_l hN (⟨fun _ => δ, fun _ => δ⟩ : Env A 1) .newest).mpr height))
  have vt := relative.transitive_l work.transitive hv
  obtain ⟨cv, Rv, mv⟩ := smdl_membership_l I hZF ⟨Ω, strength.1⟩
  have small : It_local_d I Ω v Rv κ L F :=
    (ex_local_sat_l I θ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) vt ⟨cv, mv⟩).mp moved.1
  have inaccessible := (ex_inaccessible_sat_l θ (.bound 6) (.bound 3) (.bound 4) vt).mp moved.2.1
  have below : M.MemberSubset Ω κ := by
    let p : Env A 2 := ⟨Fin.cases ξ (fun _ => w), fun _ => w⟩
    let q : Env B 2 := ⟨Fin.cases ξ' (fun _ => w'), fun _ => w'⟩
    have mapped := lift (Formula.subset (.bound 1) .newest)
      (by decide)
      (.atom ..) p q (Fin.cases hξ (fun _ => hw))
      ((Formula.satisfies_subset_iff p (.bound 1) .newest).mpr source.below)
    exact (Formula.satisfies_subset_iff (image_env_l (M := B) (N := M) Subtype.val q) (.bound 1) .newest).mp mapped
  -- 临界点的小性由工作源中的序数恒等图给出，再沿同一秩段提升三项性质。
  obtain ⟨K₀, owner⟩ := work.rebase_l ξ'.property below
    (sc_ordinal_small_l hZF work.omega work.transitive my work.theory ξ'.property
      (small.ordinals_l (ZF.modelsKP hZF) vt ⟨cv, mv⟩).1)
  exact ⟨K₀, owner, small.of_rank_l hZF owner hv relative limit ⟨cv, mv⟩,
    strength.of_rank_l hZF work.transitive hv relative limit,
    inaccessible.of_rank_l hZF work.transitive algebra.pair hv relative limit⟩

/-- 原树实际保存的所属证书沿指定复制图给出规范工作呈示。
秩源见证由证书自身读取；调用者无需重新指定或识别它们。 -/
theorem It_owner_d.copy_l {Ω c N T d Y S σ μ H ξ ℓ e κ L F : M.Domain}
    (quality : It_owner_d I Ω c ξ ℓ e)
    (mx : Smdl_d I c N T) (my : Smem_d I d Y S)
    (map : Smap_d I Ω c d N Y σ)
    (hN : (smdl_structure_l I (R := T) mx.2.1).Models KP)
    (work : Ep_source_d I Ω μ H Y S)
    (hξ : Rd_entry_d ξ κ σ) (hℓ : Rd_entry_d ℓ L σ) (he : Rd_entry_d e F σ) :
    ∃ K, Ep_source_d I Ω κ K Y S ∧ It_local_d I Ω Y S κ L F ∧
      Ex_strength_d I Ω κ L Y F ∧ Sc_inaccessible_d Ω Y L := by
  obtain ⟨N₀,T₀,model,w,z,numbers,truth⟩ := quality
  obtain ⟨eqN,eqT⟩ := smdl_unique_l I model mx
  subst N₀ T₀
  let A := smdl_structure_l I (R := T) mx.2.1
  let w₀ : A.Domain := ⟨w,numbers.member⟩
  let ξ₀ : A.Domain := ⟨ξ,map.1.1.input_mem_of_pairMember hξ⟩
  let ℓ₀ : A.Domain := ⟨ℓ,map.1.1.input_mem_of_pairMember hℓ⟩
  let e₀ : A.Domain := ⟨e,map.1.1.input_mem_of_pairMember he⟩
  let v : Fin 4 → A.Domain := Fin.cases e₀ (Fin.cases ℓ₀ (Fin.cases ξ₀ (fun _ => w₀)))
  have coordinates : (fun i => (v i).val) =
      Fin.cases e (Fin.cases ℓ (Fin.cases ξ (fun _ => w))) := by
    funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i
  have native := (rr_truth_native_l I mx.2.1 it_native_quality0_m
    it_native_quality0_closed_l v).mp (coordinates.symm ▸ truth)
  obtain ⟨δ,V,K,R,rank,height,source,loc,card,strong⟩ :=
    (it_native_quality_sat_l hN ⟨v,fun _ => v 0⟩ (.bound 3) (.bound 2) (.bound 1) .newest).mp native
  exact er_quality_copy_l hZF mx my map hN w₀ ξ₀ ℓ₀ e₀ V δ K R
    numbers source rank height loc strong card work hξ hℓ he

end YesMetaZFC.SetTheory.LargeCardinal
