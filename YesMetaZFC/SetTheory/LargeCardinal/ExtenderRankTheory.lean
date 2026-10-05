import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.Model.SetTheory.Internal.SourceRankClosure
import YesMetaZFC.Model.SetTheory.Internal.RelativeCountable

/-! # 严格秩段中的全内部分离与小定义域收集

先在所属源内计算有限真值行，再用有界公式选择实际见证。
秩界只用于把已经构造的图放回严格秩段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 完整赋值只保留程序实际使用的有限坐标，真值行是源内实际集合。 -/
theorem Ep_source_d.truth_row_l {ω κ K Z S A R E F n r i j f : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hA : M.mem A Z) (hR : M.mem R Z)
    (hE : M.IsFunctionSpace I E ω A) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hf : M.mem f E) :
    ∃ b D u T, M.mem b ω ∧ Sbound_d I F b ∧ M.mem i b ∧ M.mem j b ∧
      M.mem D Z ∧ M.mem T Z ∧ M.IsFunctionSpace I D b A ∧ M.mem u D ∧ Senv_agree_d I b f u ∧
      ∀ v, Ssat_d I A R D F n r v ↔ M.mem v T := by
  obtain ⟨b, hb, bound, hib, hjb⟩ := sbound_above_l I hZF source.omega hF hi hj
  obtain ⟨D, hD, space⟩ := source.finite_space_l hZF hA hb
  obtain ⟨_, _, L, _, program⟩ := source.program_l hZF hF
  have program := fb_program_of_l (ZF.modelsKP hZF) hF hb bound program.2.2.1
  obtain ⟨C, H, hC, _, table⟩ := source.finite_evaluation_l hZF hA hR hD program space
  obtain ⟨T, hT, hrT⟩ := table.1.2.1 r hr
  obtain ⟨u, res⟩ := ZF.exists_restriction hZF I f b
  have hu := res.isSetFunctionFromTo ((hE f).mp hf) (source.omega.transitive hZF b hb)
  exact ⟨b, D, u, T, hb, bound, hib, hjb, hD, source.transitive C hC T hT, space, (space u).mpr hu,
    fun k x hk => ⟨fun h => (res.2 k x).mpr ⟨hk, h⟩, fun h => ((res.2 k x).mp h).2⟩,
    ssat_value_l I hZF (table.seval_l hZF source.omega program space) hrT⟩

theorem Ep_source_d.rank_theory_l {ω κ K Z S α V c R : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hm : Smem_d I c V R) : Sc_theory_d I ω V R := by
  have hZ := source.transitive
  have ht := rank.transitive_l hZF hZ hV
  obtain ⟨z, hz⟩ := source.code
  have hR := source.membership_relation_l hZF hV hm
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_, source.theory.algebra.rank_l hZF hZ hV rank hα⟩
  obtain ⟨b, G, u, T, hb, bound, hib, _, hG, hT, space, hu, agree, truth⟩ :=
    source.truth_row_l hZF hV hR hE hF hr hi hi hf
  let ρ : Env M 6 := ⟨Fin.cases b (Fin.cases V (Fin.cases u (Fin.cases i (Fin.cases G (fun _ => T))))), fun _ => V⟩
  let φ : UnarySchema 6 := { body := Formula.existsMem (.bound 5) (.conj
    (se_update0_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) .newest) (.mem .newest (.bound 7))) }
  have read x : φ.denote ρ x ↔ ∃ v, M.mem v G ∧ Se_update0_d b V u i x v ∧ M.mem v T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      se_update0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have decode x (hx : M.mem x V) : φ.denote ρ x ↔ ∃ g, Senv_update_d I f i x g ∧ Ssat_d I V R E F n r g := by
    have update v := se_update0_l (g := v) (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((space u).mp hu)) hib hx
    constructor
    · intro h
      obtain ⟨v, hv, uv, ht⟩ := (read x).mp h
      obtain ⟨g, fg, hg⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
      exact ⟨g, fg, (ssat_spaces_l I hZF hF bound hE space (source.omega.transitive hZF b hb) (fun _ h => h)
        hr ((hE g).mpr hg) hv (agree.update_l I fg ((update v).mp uv))).mpr ((truth v).mpr ht)⟩
    · rintro ⟨g, fg, sat⟩
      obtain ⟨v, uv, hv⟩ := senv_update_exists_l I hZF ((space u).mp hu) hib hx
      exact (read x).mpr ⟨v, (space v).mpr hv, (update v).mpr uv, (truth v).mp
        ((ssat_spaces_l I hZF hF bound hE space (source.omega.transitive hZF b hb) (fun _ h => h)
          hr ((hE g).mpr (fg.function_l I ((hE f).mp hf) hi hx)) ((space v).mpr hv) (agree.update_l I fg uv)).mp sat)⟩
  obtain ⟨A, hA, spec⟩ := sc_separate_source_l I hZF source.omega hZ hz source.theory φ
    (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _))) ρ
    (Fin.cases (hZ ω source.omega_mem b hb) (Fin.cases hV (Fin.cases (hZ G hG u hu)
      (Fin.cases (hZ ω source.omega_mem i hi) (Fin.cases hG (fun _ => hT)))))) (hZ V hV D hD)
  exact ⟨A, rank.subset_mem_l hZ hV hD hA (fun x hx => ((spec x).mp hx).1),
    fun x => (spec x).trans (and_congr_right fun hx => decode x (ht D hD x hx))⟩

/-- 源内编号使小定义域上的图落在内部正则秩段中。 -/
theorem Ep_source_d.rank_function_l {ω κ K Z S α V D μ ι f : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hD : M.mem D V) (hμ : M.mem μ V)
    (hι : M.mem ι Z) (idx : Sc_index_d μ D ι) (hf : M.mem f Z) (fn : Fn0_d D V f) : M.mem f V := by
  obtain ⟨c, hc⟩ := source.code
  have hZ := source.transitive
  have ht := rank.transitive_l hZF hZ hV
  have history := rank
  obtain ⟨_, H, _, hH, cert⟩ := history
  have hαZ := sc_function_domain_mem_l hZF source.omega hZ hc source.theory hH (cert V hV).2.1
  have hμZ := hZ V hV μ hμ
  obtain ⟨g, hg, inj⟩ := idx.restrict_l hZF source.omega hZ hc source.theory (hZ V hV D hD) hμZ hι
  obtain ⟨e, he, hi⟩ := sc_graph_numbering_l hZF source.omega hZ hc source.theory hμZ (hZ V hV D hD) hV hg hf inj fn
  exact sc_indexed_rank_l hZF source.omega hZ hc source.theory hμZ hαZ hα.2.1 hV rank
    (regular μ (rank.ordinal_height_l hZF hZ hV idx.ordinal hμ)) hf he
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal hi) (fun p hp => by
      obtain ⟨x, hx, y, hy, pair⟩ := fn.1 p hp
      exact rank.kpair_mem_l hZF hZ hV hα (ht D hD x hx) hy (hZ f hf p hp) pair)

theorem Ep_source_d.rank_collection_l {ω κ K Z S α V c R : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hm : Smem_d I c V R) : Sc_collection_d I ω V R := by
  intro D _ small E F n r i j f A hE hF hr hi hj _ hf hA hAD total
  have hZ := source.transitive
  have ht := rank.transitive_l hZF hZ hV
  obtain ⟨z, hz⟩ := source.code
  obtain ⟨b, G, u, T, hb, bound, hib, hjb, hG, hT, space, hu, agree, truth⟩ :=
    source.truth_row_l hZF hV (source.membership_relation_l hZF hV hm) hE hF hr hi hj hf
  let ρ : Env M 7 := ⟨Fin.cases b (Fin.cases V (Fin.cases u (Fin.cases i
    (Fin.cases j (Fin.cases G (fun _ => T)))))), fun _ => V⟩
  let φ : BinarySchema 7 := { body := Formula.existsMem (.bound 7) (Formula.existsMem (.bound 8) (.conj
    (se_update0_m (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 3) (.bound 1)) (.conj
      (se_update0_m (.bound 4) (.bound 5) (.bound 1) (.bound 8) (.bound 2) .newest) (.mem .newest (.bound 10))))) }
  have read x y : φ.denote ρ x y ↔ ∃ v, M.mem v G ∧ ∃ w, M.mem w G ∧
      Se_update0_d b V u i x v ∧ Se_update0_d b V v j y w ∧ M.mem w T := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      se_update0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have decode x (hx : M.mem x V) y (hy : M.mem y V) : φ.denote ρ x y ↔ Sbin_d I V R E F n r i j f x y := by
    constructor
    · intro h
      obtain ⟨v, hv, w, hw, uv, vw, ht⟩ := (read x y).mp h
      have uv := (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((space u).mp hu)) hib hx).mp uv
      have vw := (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((space v).mp hv)) hjb hy).mp vw
      obtain ⟨g, fg, hg⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
      obtain ⟨h, gh, hh⟩ := senv_update_exists_l I hZF hg hj hy
      exact ⟨g, h, fg, gh, (ssat_spaces_l I hZF hF bound hE space (source.omega.transitive hZF b hb) (fun _ h => h)
        hr ((hE h).mpr hh) hw ((agree.update_l I fg uv).update_l I gh vw)).mpr ((truth w).mpr ht)⟩
    · rintro ⟨g, h, fg, gh, sat⟩
      obtain ⟨v, uv, hv⟩ := senv_update_exists_l I hZF ((space u).mp hu) hib hx
      obtain ⟨w, vw, hw⟩ := senv_update_exists_l I hZF hv hjb hy
      exact (read x y).mpr ⟨v, (space v).mpr hv, w, (space w).mpr hw,
        (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((space u).mp hu)) hib hx).mpr uv,
        (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) hv) hjb hy).mpr vw,
        (truth w).mp ((ssat_spaces_l I hZF hF bound hE space (source.omega.transitive hZF b hb) (fun _ h => h)
          hr ((hE h).mpr (gh.function_l I (fg.function_l I ((hE f).mp hf) hi hx) hj hy)) ((space w).mpr hw)
          ((agree.update_l I fg uv).update_l I gh vw)).mp sat)⟩
  obtain ⟨q, hq, fn, select⟩ := sc_uniform_source_l hZF source.omega hZ hz source.theory φ
    (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.conj (se_update0_delta_l ..) (.mem _ _))))) ρ
    (Fin.cases (hZ ω source.omega_mem b hb) (Fin.cases hV (Fin.cases (hZ G hG u hu)
      (Fin.cases (hZ ω source.omega_mem i hi) (Fin.cases (hZ ω source.omega_mem j hj) (Fin.cases hG (fun _ => hT)))))))
    (hZ V hV A hA) hV (fun x hx => (total x hx).imp fun y hy => ⟨hy.1, (decode x (ht A hA x hx) y hy.1).mpr hy.2⟩)
  obtain ⟨μ, ι, hμ, hι, idx⟩ := small.mono_l hAD
  have hqV := source.rank_function_l hZF hV rank hα regular hA hμ (hZ V hV ι hι) idx hq fn
  obtain ⟨C, hC, cover⟩ := (source.theory.algebra.rank_l hZF hZ hV rank hα).envelope_l hqV
  exact ⟨q, C, hqV, hC, fn.retarget_l (fun x y h => (cover x y h).2), fun x y h =>
    (decode x (ht A hA x (fn.bound_l h).1) y (fn.bound_l h).2).mp (select x y h)⟩

/-- 小外延关系的塌缩大小保持原编号，内部正则界因此控制其传递像。 -/
theorem Ep_source_d.rank_collapse_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) : Sc_collapse_d V := by
  intro A R hA hR small wf ext
  have hZ := source.transitive
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  have hμZ := hZ V hV μ hμ
  have heZ := hZ V hV e he
  obtain ⟨B, F, hB, hF, iso⟩ := source.collapse A R (hZ V hV A hA) (hZ V hV R hR)
    ⟨μ, e, hμZ, heZ, idx⟩ (fun Y hY sub => wf Y (rank.subset_mem_l hZ hV hA hY sub) sub) ext
  obtain ⟨f, hf, index⟩ := sc_index_image_l hZF source.omega hZ hc source.theory
    (hZ V hV A hA) hB hF hμZ heZ idx iso.function iso.onto
  have history := rank
  obtain ⟨_, H, _, hH, cert⟩ := history
  have hαZ := sc_function_domain_mem_l hZF source.omega hZ hc source.theory hH (cert V hV).2.1
  have hBV := sc_indexed_transitive_rank_l hZF source.omega hZ hc source.theory hμZ hαZ hα.2.1 hV rank
    (regular μ (rank.ordinal_height_l hZF hZ hV idx.ordinal hμ)) hB iso.transitive hf index
  exact ⟨B, F, hBV, rank.relation_mem_l hZF hZ hV hα hA hBV hF iso.function.1, iso⟩

end YesMetaZFC.SetTheory.LargeCardinal
