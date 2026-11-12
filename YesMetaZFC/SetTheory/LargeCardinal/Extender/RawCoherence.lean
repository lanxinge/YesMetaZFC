import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Source.RankClosure
import YesMetaZFC.Model.SetTheory.Reflection.RelativeCountable
import YesMetaZFC.Model.SetTheory.Embedding.Relative
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.Model.SetTheory.Relations.LayerMeasure
import YesMetaZFC.Model.SetTheory.Relations.FunctionCapture
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hA : M.mem A Z) (hR : M.mem R Z)
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
  have hu := res.isSetFunctionFromTo ((hE f).mp hf) (source.omega.transitive (ZF.modelsKP hZF) b hb)
  exact ⟨b, D, u, T, hb, bound, hib, hjb, hD, source.transitive C hC T hT, space, (space u).mpr hu,
    fun k x hk => ⟨fun h => (res.2 k x).mpr ⟨hk, h⟩, fun h => ((res.2 k x).mp h).2⟩,
    ssat_value_l I hZF (table.seval_l hZF source.omega program space) hrT⟩

theorem Ep_source_d.rank_theory_l {ω κ K Z S α V c R : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hm : Smem_d I c V R) : Sc_theory_d I ω V R := by
  have hZ := source.transitive
  have ht := rank.transitive_l hZ hV
  obtain ⟨z, hz⟩ := source.code
  have hR := source.membership_relation_l hZF hV hm
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_,
    (sc_algebra_mem_l I (ZF.modelsKP hZF) hm ht).mpr ((source.algebra_l (ZF.modelsKP hZF)).rank_l hZF hZ hV rank hα)⟩
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
      exact ⟨g, fg, (ssat_spaces_l I hZF hF bound hE space (source.omega.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
        hr ((hE g).mpr hg) hv (agree.update_l I fg ((update v).mp uv))).mpr ((truth v).mpr ht)⟩
    · rintro ⟨g, fg, sat⟩
      obtain ⟨v, uv, hv⟩ := senv_update_exists_l I hZF ((space u).mp hu) hib hx
      exact (read x).mpr ⟨v, (space v).mpr hv, (update v).mpr uv, (truth v).mp
        ((ssat_spaces_l I hZF hF bound hE space (source.omega.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
          hr ((hE g).mpr (fg.function_l I ((hE f).mp hf) hi hx)) ((space v).mpr hv) (agree.update_l I fg uv)).mp sat)⟩
  obtain ⟨A, hA, spec⟩ := sc_separate_source_l I hZF source.omega hZ hz source.theory φ
    (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _))) ρ
    (Fin.cases (hZ ω source.omega_mem b hb) (Fin.cases hV (Fin.cases (hZ G hG u hu)
      (Fin.cases (hZ ω source.omega_mem i hi) (Fin.cases hG (fun _ => hT)))))) (hZ V hV D hD)
  have hAV := rank.subset_mem_l hZ hV hD hA (fun x hx => ((spec x).mp hx).1)
  exact ⟨A, hAV, (ssep_relation_l I ht hm hD hAV).mpr
    (fun x => (spec x).trans (and_congr_right fun hx => decode x (ht D hD x hx)))⟩

/-- 源内编号使小定义域上的图落在内部正则秩段中。 -/
theorem Ep_source_d.rank_function_l {ω κ K Z S α V D μ ι f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hD : M.mem D V) (hμ : M.mem μ V)
    (hι : M.mem ι Z) (idx : Sc_index_d μ D ι) (hf : M.mem f Z) (fn : Fn0_d D V f) : M.mem f V := by
  obtain ⟨c, hc⟩ := source.code
  have hZ := source.transitive
  have ht := rank.transitive_l hZ hV
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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hm : Smem_d I c V R) : Sc_collection_d I ω V R := by
  have hZ := source.transitive
  have ht := rank.transitive_l hZ hV
  apply (sc_collection_mem_l I (ZF.modelsKP hZF) ht hm).mpr
  intro D hD small
  apply (sc_uniform_mem_l I hZF.1 ht hm hD).mpr
  intro E F n r i j f A hE hF hr hi hj _ hf hA hAD total
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
      exact ⟨g, h, fg, gh, (ssat_spaces_l I hZF hF bound hE space (source.omega.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
        hr ((hE h).mpr hh) hw ((agree.update_l I fg uv).update_l I gh vw)).mpr ((truth w).mpr ht)⟩
    · rintro ⟨g, h, fg, gh, sat⟩
      obtain ⟨v, uv, hv⟩ := senv_update_exists_l I hZF ((space u).mp hu) hib hx
      obtain ⟨w, vw, hw⟩ := senv_update_exists_l I hZF hv hjb hy
      exact (read x y).mpr ⟨v, (space v).mpr hv, w, (space w).mpr hw,
        (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((space u).mp hu)) hib hx).mpr uv,
        (se_update0_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) hv) hjb hy).mpr vw,
        (truth w).mp ((ssat_spaces_l I hZF hF bound hE space (source.omega.transitive (ZF.modelsKP hZF) b hb) (fun _ h => h)
          hr ((hE h).mpr (gh.function_l I (fg.function_l I ((hE f).mp hf) hi hx) hj hy)) ((space w).mpr hw)
          ((agree.update_l I fg uv).update_l I gh vw)).mp sat)⟩
  obtain ⟨q, hq, fn, select⟩ := sc_uniform_source_l hZF source.omega hZ hz source.theory φ
    (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.conj (se_update0_delta_l ..) (.mem _ _))))) ρ
    (Fin.cases (hZ ω source.omega_mem b hb) (Fin.cases hV (Fin.cases (hZ G hG u hu)
      (Fin.cases (hZ ω source.omega_mem i hi) (Fin.cases (hZ ω source.omega_mem j hj) (Fin.cases hG (fun _ => hT)))))))
    (hZ V hV A hA) hV (fun x hx => (total x hx).imp fun y hy => ⟨hy.1, (decode x (ht A hA x hx) y hy.1).mpr hy.2⟩)
  obtain ⟨μ, ι, hμ, hι, idx⟩ := small.mono_l hAD
  have hqV := source.rank_function_l hZF hV rank hα regular hA hμ (hZ V hV ι hι) idx hq fn
  obtain ⟨C, hC, cover⟩ := ((source.algebra_l (ZF.modelsKP hZF)).rank_l hZF hZ hV rank hα).envelope_l hqV
  exact ⟨q, C, hqV, hC, fn.retarget_l (fun x y h => (cover x y h).2), fun x y h =>
    (decode x (ht A hA x (fn.bound_l h).1) y (fn.bound_l h).2).mp (select x y h)⟩

/-- 小外延关系的塌缩大小保持原编号，内部正则界因此控制其传递像。 -/
theorem Ep_source_d.rank_collapse_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) {c R₀ : M.Domain}
    (model : Smem_d I c V R₀) : Sc_collapse_d I V R₀ := by
  apply (sc_collapse_mem_l I (ZF.modelsKP hZF) (rank.transitive_l source.transitive hV) model).mpr
  intro A R hA hR small wf ext
  have hZ := source.transitive
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  have hμZ := hZ V hV μ hμ
  have heZ := hZ V hV e he
  obtain ⟨B, F, hB, hF, iso⟩ := (sc_collapse_mem_l I (ZF.modelsKP hZF) hZ hc).mp source.collapse A R (hZ V hV A hA) (hZ V hV R hR)
    ⟨μ, e, hμZ, heZ, idx⟩ (fun Y hY sub => wf Y (rank.subset_mem_l hZ hV hA hY sub) sub) ext
  obtain ⟨f, hf, index⟩ := sc_index_image_l hZF source.omega hZ hc source.theory
    (hZ V hV A hA) hB hF hμZ heZ idx iso.function iso.onto
  have history := rank
  obtain ⟨_, H, _, hH, cert⟩ := history
  have hαZ := sc_function_domain_mem_l hZF source.omega hZ hc source.theory hH (cert V hV).2.1
  have hBV := sc_indexed_transitive_rank_l hZF source.omega hZ hc source.theory hμZ hαZ hα.2.1 hV rank
    (regular μ (rank.ordinal_height_l hZF hZ hV idx.ordinal hμ)) hB iso.transitive hf index
  exact ⟨B, F, hBV, rank.relation_mem_l hZ hV hα hA hBV hF iso.function.1, iso⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相对秩段及初等回拉的完整源证书 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际秩历史回收高度；内部正则性排除该高度为后继。 -/
theorem Ep_source_d.rank_height_l {ω κ K X R α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hV : M.mem V X) (rank : Vr_d X α V)
    (regular : Sc_regular_d X α) (hω : M.mem ω V) : M.mem α X ∧ M.IsLimitOrdinal α := by
  obtain ⟨c, hm⟩ := source.code
  have above := rank.ordinal_height_l hZF source.transitive hV (source.omega.isOrdinal (ZF.modelsKP hZF)) hω
  obtain ⟨B, F, hB, hF, cert⟩ := rank
  have hα := sc_function_domain_mem_l hZF source.omega source.transitive hm source.theory hF (cert V hV).2.1
  exact ⟨hα, sc_omega_bound_limit_l hZF source.omega source.transitive hm source.theory source.omega_mem hα
    (cert V hV).1 ⟨ω, above⟩ (regular ω above)⟩

/-- 包含 κ 的严格极限秩段与原源具有完全相同的有限 κ 幂子集。 -/
theorem Ep_source_d.rank_agree_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V) : Ea_agree_d ω κ V Z := by
  have hω := rank.subset_mem_l source.transitive hV hκ source.omega_mem source.below
  intro n D A hn hd sub
  have hD := rank.relations_mem_l source.transitive hV hα hω hκ (source.space_mem_l hZF hn hd)
    (fun f hf p hp => by
      obtain ⟨i, hi, x, hx, pair⟩ := ((hd f).mp hf).1 p hp
      exact ⟨i, source.omega.transitive (ZF.modelsKP hZF) n hn i hi, x, hx, pair⟩)
  exact ⟨source.transitive V hV A, fun hA => rank.subset_mem_l source.transitive hV hD hA sub⟩

/-- 严格极限秩段包含其每个字母表的全部内部有限列。 -/
theorem Ep_source_d.rank_sequence_l (hKP : M.Models KP) {ω κ K Z S α V A : M.Domain}
    (source : Ep_source_d (kp_pair_l hKP) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) (hA : M.mem A V) :
    ∃ L, M.mem L V ∧ Fseq_space_d (kp_pair_l hKP) ω A L := by
  have hZ := source.transitive
  obtain ⟨L, hL, seq⟩ := (source.sequences_l hKP).1 A (hZ V hV A hA)
  refine ⟨L, rank.relations_mem_l hZ hV hα hω hA hL (fun f hf p hp => ?_), seq⟩
  obtain ⟨n, hn, fn⟩ := (seq f).mp hf
  obtain ⟨i, hi, x, hx, pair⟩ := (fn0_of_function_l hKP fn).1 p hp
  exact ⟨i, source.omega.transitive hKP n hn i hi, x, hx, pair⟩

theorem Ep_source_d.rank_sequences_l {ω κ K Z S α V c R : M.Domain}
    (source : Ep_source_d I ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) (model : Smem_d I c V R) : Sc_sequences_d I ω V R := by
  have hZ := source.transitive
  obtain ⟨d, hc⟩ := source.code
  have a := (source.algebra_l (ZF.modelsKP hZF)).rank_l hZF hZ hV rank hα
  apply (sc_sequences_mem_l I (ZF.modelsKP hZF) source.omega (rank.transitive_l hZ hV) model hω a.pair a.union).mpr
  refine ⟨fun _ => source.rank_sequence_l (ZF.modelsKP hZF) hV rank hα hω, ?_⟩
  intro A K μ e hA hK hμ he seq hw idx
  have hkZ := hZ V hV K hK
  have hμZ := hZ V hV μ hμ
  obtain ⟨f, hf, bound⟩ := (source.sequences_l (ZF.modelsKP hZF)).2 A K μ e (hZ V hV A hA) hkZ hμZ (hZ V hV e he) seq hw idx
  obtain ⟨g, hg, inj⟩ := bound.restrict_l hZF source.omega hZ hc source.theory hkZ hμZ hf
  exact ⟨g, rank.relation_mem_l hZ hV hα hK hμ hg (fn0_of_function_l (ZF.modelsKP hZF) inj.1).1,
    Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal inj⟩

/-- 内部正则严格秩段自动成为下一次超幂可直接消费的源。 -/
theorem Ep_source_d.rank_l {ω κ K Z S α V c R μ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d Z α) (hω : M.mem ω V) (hm : Smem_d I c V R)
    (hμ : M.mem μ V) (ho : M.IsOrdinal μ) (hw : M.MemberSubset ω μ) : ∃ L, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ L V R := by
  have ht := rank.transitive_l source.transitive hV
  have theory := source.rank_theory_l hZF hV rank hα hm
  have seq := source.rank_sequences_l hZF hV rank hα hω hm
  obtain ⟨L, hs⟩ := seq.space_l I hμ
  have core := Er_source_d.of_mem_l I hZF.1 source.omega ht hm hω
    (sc_ordinal_small_l hZF source.omega ht hm theory hμ ho) hs theory
    (source.rank_collection_l hZF hV rank hα regular hm) seq (source.rank_collapse_l hZF hV rank hα regular hm)
  exact ⟨L, core, source.omega, hw, ht, hω, hμ, c, hm⟩

/-- 反塌缩的全初等图回拉全部源性质，不另给新模型的闭包证书。 -/
theorem Ep_source_d.pull_l {ω κ K Y S X c R d j μ : M.Domain}
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Y S) (hX : M.TransitiveSet X) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hμ : M.mem μ X) (ho : M.IsOrdinal μ) (hw : M.MemberSubset ω μ) : ∃ L, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ L X R := by
  have theory := target.theory.pull_l I hZF target.omega hm.1 hn.1 hj
  have image := hj.omega_l I hZF target.omega hX target.transitive hm hn hωX
  have seq := (sc_sequences_iff_l I hZF target.omega hm.1 hn.1 hj image).mpr target.sequences
  obtain ⟨L, hs⟩ := seq.space_l I hμ
  have core := Er_source_d.of_mem_l I hZF.1 target.omega hX hm hωX
    (sc_ordinal_small_l hZF target.omega hX hm theory hμ ho) hs theory
    (target.collection.pull_l I hZF target.omega hm.1 hn.1
      (smem_ext_l I hm.1 hm.2 hX hZF.1) (target.ext.native_l I hn.1.2.1) hj) seq
    ((sc_collapse_iff_l I hZF target.omega hm.1 hn.1 hj).mpr target.collapse)
  exact ⟨L, core, target.omega, hw, hX, hωX, hμ, c, hm⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 读取超幂证书所需的有限闭性

读取只用传递性、配对和全部内部有限函数及其空间。完整源与任意包含 ω
的拥有极限秩段均提供实际实例；后一实例不需要该高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Fs_read_d (ω V : M.Domain) : Prop where
  transitive : M.TransitiveSet V
  omega_mem : M.mem ω V
  pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b
  functions : ∀ n A f, M.mem n ω → M.MemberSubset A V → Fn0_d n A f → M.mem f V
  spaces : ∀ A n, M.mem A V → M.mem n ω → ∃ D, M.mem D V ∧ Ep_space_d A n D

/-- 有限读写闭包的原全称公式；所有有限函数均在当前结构中量化。 -/
def fs_read_m {d} (ω V : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isTransitive⌝ₚ(⌜V⌝ₛ) ∧ ⌜ω⌝ₛ ∈ ⌜V⌝ₛ ∧
  (∀ a ∈ ⌜V⌝ₛ, ∀ b ∈ ⌜V⌝ₛ, ∃ p ∈ ⌜V⌝ₛ, ⌜pair0_m⌝ₚ(p, a, b)) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∀ A f, A ⊆ ⌜V⌝ₛ → ⌜fn0_m⌝ₚ(n, A, f) → f ∈ ⌜V⌝ₛ) ∧
  (∀ A ∈ ⌜V⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∃ D ∈ ⌜V⌝ₛ, ∀ f, f ∈ D ↔ ⌜fn0_m⌝ₚ(n, A, f))⟫
derive_free_closed fs_read_m

theorem fs_read_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V : Term d) :
    Formula.satisfies ρ (fs_read_m ω V) ↔ Fs_read_d (ω.eval ρ) (V.eval ρ) := by
  simp only [fs_read_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_iff_iff, pair0_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨t, w, p, f, s⟩ => ⟨t, w, (fun a b ha hb => p a ha b hb),
      (fun n A g hn => f n hn A g), (fun A n hA hn => s A hA n hn)⟩,
    fun h => ⟨h.transitive, h.omega_mem, (fun a ha b hb => h.pair a b ha hb),
      (fun n hn A f => h.functions n A f hn), (fun A hA n hn => h.spaces A n hA hn)⟩⟩

/-- 实际有限层进入传递源的原解释；此方向只需外延性和传递性。 -/
theorem Fs_read_d.source_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) (ω V : (rt_model_l X nx).Domain)
    (h : Fs_read_d ω.val V.val) : Fs_read_d ω V := by
  let N := rt_model_l X nx
  have en := rt_model_ext_l hE hX nx
  refine ⟨(fun x hx y hy => h.transitive x.val hx y.val hy), h.omega_mem, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨p, hp, pair⟩ := h.pair a.val b.val ha hb
    let q : N.Domain := ⟨p, hX V.val V.property p hp⟩
    let ρ : Env N 3 := ⟨Fin.cases q (Fin.cases a (fun _ => b)), fun _ => ω⟩
    exact ⟨q, hp, (pair0_sat_l en ρ .newest (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l hX nx (pair0_delta_l ..) ρ).mpr ((pair0_sat_l hE ..).mpr pair))⟩
  · intro n A f hn sub fn
    exact h.functions n.val A.val f.val hn
      (fun x hx => sub ⟨x, hX A.val A.property x hx⟩ hx) ((rt_fn_l hX nx hE n A f).mp fn)
  · intro A n hA hn
    obtain ⟨D, hD, space⟩ := h.spaces A.val n.val hA hn
    exact ⟨⟨D, hX V.val V.property D hD⟩, hD, fun f =>
      (space f.val).trans (rt_fn_l hX nx hE n A f).symm⟩

theorem Fs_read_d.kpair_l {ω V a b : M.Domain} (h : Fs_read_d ω V)
    (ha : M.mem a V) (hb : M.mem b V) : ∃ p, M.mem p V ∧ KPair_d M p a b := by
  obtain ⟨s, hs, singleton⟩ := h.pair a a ha ha
  obtain ⟨t, ht, both⟩ := h.pair a b ha hb
  obtain ⟨p, hp, outer⟩ := h.pair s t hs ht
  exact ⟨p, hp, s, t, (fun x => (singleton x).trans ⟨fun h => h.elim id id, Or.inl⟩), both, outer⟩

theorem Ep_source_d.read_source_l (hZF : M.Models ZF) {ω κ K V W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K V W) : Fs_read_d ω V := by
  refine ⟨source.transitive, source.omega_mem, (source.algebra_l (ZF.modelsKP hZF)).pair,
    fun n A f hn hA hf => sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union
      source.omega_mem hA hn hf, fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.finite_space_l hZF hA hn
  exact ⟨D, hD, fun f => (space f).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩⟩

theorem Fs_read_d.rank_l (hZF : M.Models ZF) {ω Z α V : M.Domain}
    (source : Fs_read_d ω Z) (hω₀ : M.IsOmega ω)
    (union : ∀ a, M.mem a Z → ∃ p, M.mem p Z ∧ M.IsUnionOf p a)
    (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Fs_read_d ω V := by
  have vt := rank.transitive_l source.transitive hV
  have pair a b (ha : M.mem a V) (hb : M.mem b V) : ∃ p, M.mem p V ∧ Pair_d M p a b := by
    obtain ⟨p, hp, code⟩ := source.pair a b (source.transitive V hV a ha) (source.transitive V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF source.transitive hV hα ha hb hp code, code⟩
  have un a (ha : M.mem a V) : ∃ p, M.mem p V ∧ M.IsUnionOf p a := by
    obtain ⟨p, hp, code⟩ := union a (source.transitive V hV a ha)
    exact ⟨p, rank.union_mem_l source.transitive hV ha hp code, code⟩
  refine ⟨vt, hω, pair, fun n A f hn hA hf => sc_finite_function_l (ZF.modelsKP hZF) hω₀ vt pair un hω hA hn hf,
    fun A n hA hn => ?_⟩
  obtain ⟨D, hD, space⟩ := source.spaces A n (source.transitive V hV A hA) hn
  refine ⟨D, rank.relations_mem_l source.transitive hV hα hω hA hD (fun f hf p hp => ?_), space⟩
  obtain ⟨i, hi, x, hx, code⟩ := ((space f).mp hf).1 p hp
  exact ⟨i, hω₀.transitive (ZF.modelsKP hZF) n hn i hi, x, hx, code⟩

theorem Ep_source_d.rank_read_source_l (hZF : M.Models ZF) {ω κ K Z W α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) : Fs_read_d ω V :=
  (source.read_source_l hZF).rank_l hZF source.omega (source.algebra_l (ZF.modelsKP hZF)).union hV rank hα hω

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系后继的有限读写闭性

有限空间用一个固定句子整体传递，量化下一层的全部新参数。解码时先取得
配对、并集和真实 ω，再以背景内部自然数归纳回收全部有限图。因此函数空间
包括背景内部非标准有限长度；不要求高模型传递或对外部 ω 列封闭。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def fs_read0_m {d} (ω : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜ω⌝ₛ) ∧
  (∀ a b, ∃ p, ⌜pair0_m⌝ₚ(p, a, b)) ∧
  (∀ a, ∃ p, ⌜Formula.isUnion⌝ₚ(p, a)) ∧
  (∀ A, ∀ n ∈ ⌜ω⌝ₛ, ∃ D, ∀ f, f ∈ D ↔ ⌜fn0_m⌝ₚ(n, A, f))⟫
derive_free_closed fs_read0_m

theorem fs_read0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω : Term d) :
    Formula.satisfies ρ (fs_read0_m ω) ↔
      M.IsOmega (ω.eval ρ) ∧ M.IsLimitOrdinal (ω.eval ρ) ∧
      (∀ a b, ∃ p, Pair_d M p a b) ∧
      (∀ a, ∃ p, M.IsUnionOf p a) ∧
      ∀ A n, M.mem n (ω.eval ρ) → ∃ D, Ep_space_d A n D := by
  simp only [fs_read0_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff, pair0_sat_l hE,
    Formula.satisfies_isUnion_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hE, Definitional.Term.eval_weaken, Ep_space_d]; rfl

/-- 两个有限闭包方向都涉及全部背景内部自然数，而非外部逐个标准长度。 -/
theorem fs_read0_relative_l (hKP : M.Models KP) {Ω Γ : M.Domain} (hΩ : M.IsOmega Ω) (trans : M.TransitiveSet Γ)
    (nc : Nonempty {x // M.mem x Γ}) (w : (rt_model_l Γ nc).Domain) :
    Formula.satisfies (⟨fun _ => w, fun _ => w⟩ : Env (rt_model_l Γ nc) 1) (fs_read0_m .newest) ↔
      M.IsOmega w.val ∧ Fs_read_d w.val Γ ∧
        ∀ a, M.mem a Γ → ∃ p, M.mem p Γ ∧ M.IsUnionOf p a := by
  have ext := rt_model_ext_l hKP.1 trans nc
  have pair (p a b : (rt_model_l Γ nc).Domain) :
      Pair_d (rt_model_l Γ nc) p a b ↔ Pair_d M p.val a.val b.val := by
    let ρ : Env (rt_model_l Γ nc) 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => w⟩
    have read := (pair0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l trans nc (pair0_delta_l ..) ρ).trans (pair0_sat_l hKP.1 ..))
    exact read
  rw [fs_read0_sat_l ext]
  constructor
  · rintro ⟨localω, limit, pairs, unions, spaces⟩
    have limit := (rt_limit_l trans nc hKP w).mp limit
    -- 相对自然数集既是实际极限序数，又在本层中最小，故正是背景 ω。
    have real : M.IsOmega w.val := by
      rcases (hΩ.isOrdinal hKP).trichotomy hKP.1 limit.1 (KP.difference_exists_d hKP)
        (KP.intersection_exists_d hKP Ω w.val) with eq | lt | gt
      · exact hKP.1.eq_of_same_members Ω w.val eq ▸ hΩ
      · let v : (rt_model_l Γ nc).Domain := ⟨Ω, trans w.val w.property Ω lt⟩
        have hv := rt_omega_l trans nc hKP.1 v hΩ
        have eq := ext.eq_of_same_members v w (fun x => ⟨hv.2 w localω.1 x, localω.2 v hv.1 x⟩)
        exact congrArg Subtype.val eq ▸ hΩ
      · exact (KP.mem_irrefl_d hKP w.val
          (hΩ.subset_limitOrdinal hKP limit w.val gt)).elim
    have hp a b (ha : M.mem a Γ) (hb : M.mem b Γ) : ∃ p, M.mem p Γ ∧ Pair_d M p a b := by
      obtain ⟨p, code⟩ := pairs ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨p.val, p.property, (pair p ⟨a, ha⟩ ⟨b, hb⟩).mp code⟩
    have hu a (ha : M.mem a Γ) : ∃ p, M.mem p Γ ∧ M.IsUnionOf p a := by
      obtain ⟨p, code⟩ := unions ⟨a, ha⟩
      exact ⟨p.val, p.property, (rt_union_l trans nc p ⟨a, ha⟩).mp code⟩
    have finite {n A f} := sc_finite_function_l hKP (A := A) (n := n) (f := f)
      real trans hp hu w.property
    refine ⟨real, ⟨trans, w.property, hp, fun _ _ _ hn hA hf => finite hA hn hf, ?_⟩, hu⟩
    intro A n hA hn
    let a : (rt_model_l Γ nc).Domain := ⟨A, hA⟩
    let m : (rt_model_l Γ nc).Domain := ⟨n, trans w.val w.property n hn⟩
    obtain ⟨D, code⟩ := spaces a m hn
    refine ⟨D.val, D.property, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · exact (rt_fn_l trans nc hKP.1 m a ⟨f, trans D.val D.property f hf⟩).mp
        ((code ⟨f, trans D.val D.property f hf⟩).mp hf)
    · let g : (rt_model_l Γ nc).Domain := ⟨f, finite (trans A hA) hn hf⟩
      exact (code g).mpr ((rt_fn_l trans nc hKP.1 m a g).mpr hf)
  · rintro ⟨hω, fs, unions⟩
    refine ⟨rt_omega_l trans nc hKP.1 w hω,
      (rt_limit_l trans nc hKP w).mpr (hω.isLimitOrdinal hKP), ?_, ?_, ?_⟩
    · intro a b
      obtain ⟨p, hp, code⟩ := fs.pair a.val b.val a.property b.property
      exact ⟨⟨p, hp⟩, (pair ⟨p, hp⟩ a b).mpr code⟩
    · intro a
      obtain ⟨p, hp, code⟩ := unions a.val a.property
      exact ⟨⟨p, hp⟩, (rt_union_l trans nc ⟨p, hp⟩ a).mpr code⟩
    · intro a n hn
      obtain ⟨D, hD, code⟩ := fs.spaces a.val n.val a.property hn
      exact ⟨⟨D, hD⟩, fun f => (code f.val).trans (rt_fn_l trans nc hKP.1 n a f).symm⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 原关系边传递固定有限闭包句子；新层及其 ω 来自同一完整实现图。 -/
theorem Fs_read_d.map_layer_l {ω c Y S c' Z T j B Γ H H' k k' : M.Domain}
    (source : Fs_read_d ω B) (hω : M.IsOmega ω)
    (unions : ∀ a, M.mem a B → ∃ p, M.mem p B ∧ M.IsUnionOf p a)
    (model : Smdl_d I c Y S) (next : Smdl_d I c' Z T) (embed : Smap_d I ω c c' Y Z j)
    (left : Rr_layer_d I B Y S H k) (right : Rr_layer_d I Γ Z T H' k')
    (hHH : Rd_entry_d H H' j) :
    Fs_read_d ω Γ ∧ (∀ a, M.mem a Γ → ∃ p, M.mem p Γ ∧ M.IsUnionOf p a) ∧
      ∃ x y, Rd_entry_d ω x k ∧ Rd_entry_d x y j ∧ Rd_entry_d ω y k' := by
  obtain ⟨x, hx, hwx⟩ := left.injection.1.2.2 ω source.omega_mem
  obtain ⟨y, _, hxy⟩ := embed.1.1.2.2 x hx
  obtain ⟨w, hw, _⟩ := (right.image y).mp
    ((embed.relation_l I hZF hω model next hxy hHH).mp ((left.image x).mpr ⟨ω, source.omega_mem, hwx⟩))
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω, source.omega_mem⟩⟩
  let ng : Nonempty {x // M.mem x Γ} := ⟨⟨w, hw⟩⟩
  let ρ : Env (rt_model_l B nb) 1 := ⟨fun _ => ⟨ω, source.omega_mem⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  have valid := (fs_read0_relative_l (ZF.modelsKP hZF) hω source.transitive nb ⟨ω, source.omega_mem⟩).mpr ⟨hω, source, unions⟩
  obtain ⟨η, values, truth⟩ := embed.relative_image_l hZF hω model next left right nb ng hHH
    (fs_read0_m .newest) (by simp -implicitDefEqProofs) ρ
  have same := Formula.closed_env_l (fs_read0_m .newest) (by simp -implicitDefEqProofs)
    (show (⟨fun _ => η.bound 0, fun _ => η.bound 0⟩ : Env (rt_model_l Γ ng) 1).bound = η.bound from
      funext fun i => congrArg η.bound (Subsingleton.elim 0 i))
  obtain ⟨real, fs, union⟩ := (fs_read0_relative_l (ZF.modelsKP hZF) hω right.transitive ng (η.bound 0)).mp
    (same.mpr (truth.mp valid))
  have eq : (η.bound 0).val = ω :=
    hZF.1.eq_of_same_members _ _ (fun z => ⟨real.2 ω hω.1 z, hω.2 _ real.1 z⟩)
  exact ⟨eq ▸ fs, union, by simpa only [eq] using values 0⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原秩切片的实际运算、相对幂集与有限空间

所属模型内的极限秩段给出具体运算和空间；切片语义把这些见证逐项送到
已构造的关系码。集合代数取自该秩段的实际证书，所属模型只需 KP。
高度只需是包含 ω 的极限，不额外要求正则或外部闭性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem er_cut_closure_l {N R Γ c S : M.Domain} (nx : ∃ x, M.mem x N)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (U α w : (smdl_structure_l I (R := R) nx).Domain)
    (rank : V_d (kp_pair_l hN) α U)
    (limit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal α)
    (omega : (smdl_structure_l I (R := R) nx).IsOmega w)
    (above : (smdl_structure_l I (R := R) nx).mem w U)
    (algebra : Sc_algebra_d U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (model : Smdl_d I c Γ S)
    (relation : ∀ x y, M.PairMember I x y S ↔ M.mem x Γ ∧ M.mem y Γ ∧ M.PairMember I x y R) :
    Fs_read_d w U ∧ Rf_ext_d I Γ S ∧
      (∀ η : Env (smdl_structure_l I (R := S) model.2.1) 0,
        Formula.satisfies η (.conj sc_algebra_m sc_power_m)) ∧
      Rr_truth_d I Γ S (fs_read0_m .newest) (fun _ : Fin 1 => w.val) := by
  let N₀ := smdl_structure_l I (R := R) nx
  let J := kp_pair_l hN
  have trans := v_transitive_l J rank
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨w, above⟩⟩
  have power := sc_v_power_l hN limit rank
  have read : Fs_read_d w U := by
    refine ⟨trans, above, algebra.pair,
      fun _ _ _ hn hA hf => sc_finite_function_l hN omega trans algebra.pair algebra.union above hA hn hf, ?_⟩
    intro A n hA hn
    exact v_fspace_exists_l J hN rank limit (trans w above n hn) hA
  refine ⟨read, ?_, ?_, ?_⟩
  · intro x hx y hy same
    let x' : N₀.Domain := ⟨x, ((carrier x).mp hx).1⟩
    let y' : N₀.Domain := ⟨y, ((carrier y).mp hy).1⟩
    have eq : x' = y' := hN.1.eq_of_same_members x' y' (fun z => by
      constructor
      · intro hzx
        have hz := (carrier z.val).mpr ⟨z.property, trans x' ((carrier x).mp hx).2 z hzx⟩
        exact ((relation z.val y).mp ((same z.val hz).mp ((relation z.val x).mpr ⟨hz, hx, hzx⟩))).2.2
      · intro hzy
        have hz := (carrier z.val).mpr ⟨z.property, trans y' ((carrier y).mp hy).2 z hzy⟩
        exact ((relation z.val x).mp ((same z.val hz).mpr ((relation z.val y).mpr ⟨hz, hy, hzy⟩))).2.2)
    exact congrArg (fun z : N₀.Domain => z.val) eq
  · intro η
    let ρ : Env (rt_model_l U nu) 0 := ⟨Fin.elim0, fun _ => ⟨w, above⟩⟩
    have valid : Formula.satisfies ρ (.conj sc_algebra_m sc_power_m) :=
      ⟨(sc_algebra_sat_l hN trans nu ρ).mpr algebra, (sc_power_sat_l trans nu ρ).mpr power⟩
    have moved := (rr_cut_formula_l I nx U nu model.2.1 carrier relation (.conj sc_algebra_m sc_power_m) ρ).mp valid
    exact (Formula.closed_env_l (.conj sc_algebra_m sc_power_m)
      (by simp -implicitDefEqProofs [sc_algebra_m, Definitional.Formula.FreeClosed])
      (funext fun i => Fin.elim0 i)).mp moved
  · rcases w with ⟨v, hv⟩
    let ρ : Env (rt_model_l U nu) 1 := ⟨fun _ => ⟨⟨v, hv⟩, above⟩, fun _ => ⟨⟨v, hv⟩, above⟩⟩
    have valid := (fs_read0_relative_l hN omega trans nu ⟨⟨v, hv⟩, above⟩).mpr ⟨omega, read, algebra.union⟩
    exact ⟨fun _ => (carrier v).mpr ⟨hv, above⟩,
      (rr_cut_formula_l I nx U nu model.2.1 carrier relation (fs_read0_m .newest) ρ).mp valid⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定传递地模型的有限读写闭性

全部背景内部有限图先由配对、并集和内部自然数归纳回收，再读取地模型
自己的函数空间。因此不会把地模型内部的幂集当作背景的完整幂集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (ground : (rt_model_l X nx).Models ZF)
include hZF hX ground

/-- 传递 ZF 地模型的自然数集就是背景自然数集，无须外加 ω 正确性。 -/
theorem fs_omega_relative_l (ω : (rt_model_l X nx).Domain) (localω : (rt_model_l X nx).IsOmega ω) :
    M.IsOmega ω.val := by
  have limit := (rt_limit_l hX nx (ZF.modelsKP hZF) ω).mp (localω.isLimitOrdinal (ZF.modelsKP ground))
  obtain ⟨w, hw⟩ := ZF.exists_omega hZF
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).trichotomy hZF.1 limit.1 (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) w ω.val) with eq | lt | gt
  · exact hZF.1.eq_of_same_members w ω.val eq ▸ hw
  · let v : (rt_model_l X nx).Domain := ⟨w, hX ω.val ω.property w lt⟩
    have hv := rt_omega_l hX nx hZF.1 v hw
    have eq := ground.1.eq_of_same_members v ω (fun x => ⟨hv.2 ω localω.1 x, localω.2 v hv.1 x⟩)
    exact congrArg Subtype.val eq ▸ hw
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω.val (hw.subset_limitOrdinal (ZF.modelsKP hZF) limit ω.val gt)).elim

theorem fs_read_relative_l (ω : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val) :
    Fs_read_d ω.val X := by
  have pair a b (ha : M.mem a X) (hb : M.mem b X) : ∃ p, M.mem p X ∧ Pair_d M p a b := by
    obtain ⟨p, code⟩ := KP.exists_pair (ZF.modelsKP ground) ⟨a, ha⟩ ⟨b, hb⟩
    let ρ : Env (rt_model_l X nx) 3 := ⟨Fin.cases p (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩)), fun _ => ω⟩
    exact ⟨p.val, p.property, (pair0_sat_l hZF.1 _ .newest (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l hX nx (pair0_delta_l ..) ρ).mp
        ((pair0_sat_l ground.1 ρ .newest (.bound 1) (.bound 2)).mpr code))⟩
  have un a (ha : M.mem a X) : ∃ p, M.mem p X ∧ M.IsUnionOf p a := by
    obtain ⟨p, code⟩ := KP.exists_union (ZF.modelsKP ground) ⟨a, ha⟩
    exact ⟨p.val, p.property, (rt_union_l hX nx p ⟨a, ha⟩).mp code⟩
  have finite {n A f} := sc_finite_function_l (ZF.modelsKP hZF) (A := A) (n := n) (f := f) hω hX pair un ω.property
  refine ⟨hX, ω.property, pair, fun _ _ _ hn hA hf => finite hA hn hf, fun A n hA hn => ?_⟩
  let a : (rt_model_l X nx).Domain := ⟨A, hA⟩
  let m : (rt_model_l X nx).Domain := ⟨n, hX ω.val ω.property n hn⟩
  obtain ⟨D, space⟩ := ZF.exists_functionSpace ground (kp_pair_l (ZF.modelsKP ground)) m a
  refine ⟨D.val, D.property, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · exact (rt_fn_l hX nx hZF.1 m a ⟨f, hX D.val D.property f hf⟩).mp
      (fn0_of_function_l (ZF.modelsKP ground) ((space ⟨f, hX D.val D.property f hf⟩).mp hf))
  · let g : (rt_model_l X nx).Domain := ⟨f, finite (hX A hA) hn hf⟩
    exact (space g).mpr (fn0_function_l (ZF.modelsKP ground) ((rt_fn_l hX nx hZF.1 m a g).mpr hf))

theorem fs_rank_relative_l (ω : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val)
    {α V : M.Domain} (hV : M.mem V X) (rank : Vr_d X α V)
    (limit : M.IsLimitOrdinal α) (above : M.mem ω.val V) : Fs_read_d ω.val V := by
  apply (fs_read_relative_l hZF hX nx ground ω hω).rank_l hZF hω _ hV rank limit above
  intro a ha
  obtain ⟨p, code⟩ := KP.exists_union (ZF.modelsKP ground) ⟨a, ha⟩
  exact ⟨p.val, p.property, (rt_union_l hX nx p ⟨a, ha⟩).mp code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定地模型的实际扩展器源初值

有限序列空间由原模型的 ZF 构造，全部背景内部有限图由有限读写闭包回收。
小关系的坍塌在原模型内部实施。两者均不要求原模型对外部 ω 列封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- ZF 的有限列及其实际序数编号组成同一个全称原语言句子。 -/
theorem sc_sequences_models_l (hZF : M.Models ZF) {w : M.Domain} (hw : M.IsOmega w) :
    Formula.satisfies (⟨fun _ => w, fun _ => w⟩ : Env M 1) sc_seq0_m := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  simp only [sc_seq0_m, sc_fseq0_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1]
  intro A
  obtain ⟨K, seq⟩ := ZF.fseq_space_exists_l J hZF hw A
  refine ⟨K, fun f => (seq f).trans (exists_congr fun n => and_congr_right fun _ =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩), ?_⟩
  simp only [sc_seq_index_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_subset_iff, sc_index_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  intro ν q bound index
  obtain ⟨f, fn⟩ := ZF.fseq_ordinal_bound_l J hZF hw index.ordinal bound
    (index.bound_l (ZF.modelsKP hZF)) seq
  exact ⟨f, Sc_index_d.of_injection_l (ZF.modelsKP hZF) index.ordinal fn⟩

/-- 坍塌只在模型内部进行；不要求原关系在背景中良基。 -/
theorem sc_collapse_models_l (hZF : M.Models ZF) (ρ : Env M 0) : Formula.satisfies ρ sc_collapse_m := by
  simp only [sc_collapse_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, wf_rel_sat_l hZF.1, wc_ext_sat_l hZF.1, wc_iso_sat_l hZF.1]
  exact fun _ _ _ wf ext => wc_iso_exists_l hZF wf ext

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (ground : (rt_model_l X nx).Models ZF)
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "J" => kp_pair_l (ZF.modelsKP ground)
include hZF hX ground

theorem fs_sequences_relative_l (ω : (N).Domain) (hω : M.IsOmega ω.val)
    {c R : M.Domain} (model : Smem_d I c X R) : Sc_sequences_d I ω.val X R := by
  have hw := rt_omega_l hX nx hZF.1 ω hω
  let ρ : Env N 1 := ⟨fun _ => ω, fun _ => ω⟩
  exact ⟨fun _ => ω.property, (smem_formula_l I model nx sc_seq0_m ρ).mp
    (sc_sequences_models_l ground hw)⟩

omit hZF hX in
theorem fs_collapse_relative_l {𝒞 : OrderedPairConvention} (J₀ : 𝒞.Interpretation M)
    {c R : M.Domain} (model : Smem_d J₀ c X R) : Sc_collapse_d J₀ X R := by
  intro ny η
  let ρ : Env N 0 := ⟨η.bound, η.free⟩
  apply (smem_formula_l J₀ model nx sc_collapse_m ρ).mp
  exact sc_collapse_models_l ground ρ

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原关系 ZFC 证书自动给出完整源；背景程序自然数与模型自然数分别保留。 -/
theorem Zc_model_d.source_l {Ω c X R w z : M.Domain} (hΩ : M.IsOmega Ω)
    (numbers : Rr_layer_d I Ω X R w z) (h : Zc_model_d I Ω c X R) :
    ∃ K, Er_source_d I Ω w w K X R := by
  let N := smdl_structure_l I (R := R) h.model.2.1
  let a : N.Domain := ⟨w, numbers.member⟩
  have ground := ZFC.models_zf_l (h.native_l I hZF hΩ)
  have ha : N.IsOmega a := numbers.omega_l I (ZF.modelsKP hZF) hΩ (h.ext.native_l I h.model.2.1)
  have seq : Sc_sequences_d I w X R :=
    (rr_truth_native_l I h.model.2.1 sc_seq0_m sc_seq0_closed_l (fun _ => a)).mpr
      (sc_sequences_models_l ground ha)
  obtain ⟨f, fn, graph⟩ := fn0_identity_l (ZF.modelsKP ground) a
  have small : Rf_small_d I X R w := by
    apply (rf_small_native_l I h.model.2.1 a).mpr
    simp only [sc_small_m, Formula.satisfies_exists_iff]
    refine ⟨a, f, ?_⟩
    exact (sc_index_sat_l (ZF.modelsKP ground) _ (.bound 1) (.bound 2) .newest).mpr
      (Sc_index_d.of_injection_l (ZF.modelsKP ground) (ha.isOrdinal (ZF.modelsKP ground))
        ⟨fn0_function_l (ZF.modelsKP ground) fn,
          fun x y v hx hy => ((graph x v).mp hx).2.trans ((graph y v).mp hy).2.symm⟩)
  obtain ⟨K, finite⟩ := seq.space_l I numbers.member
  exact ⟨K, Er_source_d.of_layer_l I (ZF.modelsKP hZF) hΩ h.ext numbers small finite
    (h.theory_l hZF hΩ) (h.collection_l hZF hΩ) seq
    (fun _ ρ => sc_collapse_models_l ground ρ)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 拥有的模型码及完整源沿外层初等图回拉

原结构码的两个坐标及原关系同时回拉；实际限制保持完整内部初等性。
字面隶属读取只在目标确有该关系时反射，原生节点不需要此条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 结构码的两个坐标共同回拉；关系只要求落在实际载体的平方中。 -/
theorem ep_set_model_pull_l {ω V R W S c d π a b B Q : M.Domain}
    (hω : M.IsOmega ω) (ht : M.TransitiveSet V) (kt : M.TransitiveSet W)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W π)
    (hab : Rd_entry_d a b π) (mb : Smdl_d I b B Q) :
    ∃ A P, Smdl_d I a A P ∧ Rd_entry_d A B π ∧ Rd_entry_d P Q π := by
  obtain ⟨A, P, _, _, pair, hAB, hPQ⟩ := hj.kpair_preimage_l hZF hω ht kt mv mw hab mb.1
  have nonempty := smap_delta_l I hZF hω ht kt mv mw hj
    (Formula.existsMem (Term.newest : Term 1) .truth) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])
    (.existsMem _ .truth) ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => B, fun _ => B⟩ (fun _ => hAB)
  simp only [Formula.satisfies_existsMem_iff, Formula.satisfies_truth_iff, and_true] at nonempty
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := smap_delta_l I hZF hω ht kt mv mw hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases P (fun _ => A), fun _ => A⟩ ⟨Fin.cases Q (fun _ => B), fun _ => B⟩ (Fin.cases hPQ (fun _ => hAB))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨x, y, pair⟩ := mb.2.2.1 p hp
    have xy := mb.2.2.2 x y ⟨p, pair, hp⟩
    exact ⟨x, xy.1, y, xy.2, pair⟩)
  refine ⟨A, P, ⟨pair, nonempty.mpr mb.2.1, ?_⟩, hAB, hPQ⟩
  exact ⟨fun p hp => (shape p hp).elim fun x hx => hx.2.elim fun y hy => ⟨x, y, hy.2⟩,
    fun x y ⟨p, pair, hp⟩ => by
      obtain ⟨x', hx, y', hy, pair'⟩ := shape p hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
      exact ⟨hx, hy⟩⟩

/-- 仅在目标关系确实是隶属时，逐点反射得到原关系的字面隶属读取。 -/
theorem ep_set_membership_pull_l {ω V R W S c d π a A P b B Q : M.Domain}
    (hω : M.IsOmega ω) (ht : M.TransitiveSet V) (kt : M.TransitiveSet W)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W π)
    (ma : Smdl_d I a A P) (mb : Smem_d I b B Q)
    (hAB : Rd_entry_d A B π) (hPQ : Rd_entry_d P Q π) : Smem_d I a A P := by
  have value x (hx : M.mem x A) := hj.1.1.2.2 x (ht A (hj.1.1.input_mem_of_pairMember hAB) x hx)
  refine ⟨ma, fun x y => ⟨fun hxy => ?_, fun ⟨hx, hy, hxy⟩ => ?_⟩⟩
  · obtain ⟨hx, hy⟩ := ma.2.2.2 x y hxy
    obtain ⟨x', _, hxx⟩ := value x hx
    obtain ⟨y', _, hyy⟩ := value y hy
    exact ⟨hx, hy, (hj.member_l I hZF hω mv mw hxx hyy).mpr
      ((mb.2 x' y').mp ((hj.entry_l hZF hω ht kt mv mw hxx hyy hPQ).mp hxy)).2.2⟩
  · obtain ⟨x', _, hxx⟩ := value x hx
    obtain ⟨y', _, hyy⟩ := value y hy
    exact (hj.entry_l hZF hω ht kt mv mw hxx hyy hPQ).mpr ((mb.2 x' y').mpr
      ⟨(hj.member_l I hZF hω mv mw hxx hAB).mp hx,
        (hj.member_l I hZF hω mv mw hyy hAB).mp hy, (hj.member_l I hZF hω mv mw hxx hyy).mp hxy⟩)

theorem ep_set_source_pull_l {ω κ K V R μ K' W S c d π a b B Q J : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K V R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' W S)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W π)
    (hab : Rd_entry_d a b π) (mb : Smem_d I b B Q) (child : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J B Q) :
    ∃ A P H p, Smem_d I a A P ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω H A P ∧ Rd_entry_d A B π ∧
      M.IsRestrictionOf I p π A ∧ Smap_d I ω a b A B p := by
  obtain ⟨A, P, raw, hAB, hPQ⟩ := ep_set_model_pull_l hZF source.omega source.transitive target.transitive mv mw hj hab mb.1
  have ma := ep_set_membership_pull_l hZF source.omega source.transitive target.transitive mv mw hj raw mb hAB hPQ
  have hωπ := hj.omega_l I hZF source.omega source.transitive target.transitive mv mw source.omega_mem
  have hωA := (hj.member_l I hZF source.omega mv mw hωπ hAB).mpr child.omega_mem
  let φ : Formula 1 1 := Formula.forallMem .newest (Formula.subset .newest (.bound 1))
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive mv mw hj φ
    (by simp -implicitDefEqProofs [φ]) (.forallMem _ (.atom ..))
    ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => B, fun _ => B⟩ (fun _ => hAB)
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_subset_iff] at tr
  have ht : M.TransitiveSet A := tr.mpr child.transitive
  obtain ⟨p, restriction, hp⟩ := ep_set_restriction_l hZF source target mv mw hj ma.1 mb.1 hAB
    (ep_set_membership_l hZF source target mv mw hj ma mb hAB)
  obtain ⟨H, hs⟩ := child.pull_l hZF ht hωA ma mb hp hωA (source.omega.isOrdinal (ZF.modelsKP hZF)) (fun _ h => h)
  exact ⟨A, P, H, p, ma, hs, hAB, restriction, hp⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系所属扩展器的全部实际支撑测度

先在所属模型内编码任意背景内部有限支撑，再读取同一扩展器的测度。
函数码、内部测度及坐标迹均唯一，故背景替换装成一张真实集合图；
原关系模型的高层对象不被当作背景集合读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}
variable (I : kpair_convention_l.Interpretation M)

def Er_measure_d (ω κ L N T F k a U : M.Domain) : Prop :=
  ∃ n m b u D t, M.mem n ω ∧ Fn0_d n L a ∧ Rd_entry_d n m k ∧
    Rf_fun_d I N T m b ∧ Rc_graph_d I N T k b a ∧ Rf_val_d I N T b u F ∧
    Ep_space_d κ n D ∧ M.IsRestrictionOf I t k D ∧
    ∀ A, M.mem A U ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u T ∧ Rt_trace_d I D t T B A

def er_measure_m {d} (ω κ L N T F k a U : Term d) : Formula 1 d := set[d] ⟪
  ∃ n m b u D t, n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(n, m, ⌜k⌝ₛ) ∧
    ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, m, b) ∧
    ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜k⌝ₛ, b, ⌜a⌝ₛ) ∧
    ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, b, u, ⌜F⌝ₛ) ∧
    ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) ∧ ⌜Formula.isRestriction kpair_convention_l⌝ₚ(t, ⌜k⌝ₛ, D) ∧
    (∀ A, A ∈ ⌜U⌝ₛ ↔ (∃ B ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(B, u, ⌜T⌝ₛ) ∧
      ⌜rt_trace_m (𝒞 := kpair_convention_l)⌝ₚ(D, t, ⌜T⌝ₛ, B, A)))⟫
derive_free_closed er_measure_m

theorem er_measure_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L N T F k a U : Term d) :
    Formula.satisfies ρ (er_measure_m ω κ L N T F k a U) ↔
      Er_measure_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ)
        (F.eval ρ) (k.eval ρ) (a.eval ρ) (U.eval ρ) := by
  simp only [er_measure_m, Er_measure_d, Formula.satisfies_exists_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry0_sat_l hE,
    rf_fun_sat_l I, rf_val_sat_l I, rc_graph_sat_l I hE, ep_space_sat_l hE,
    Formula.satisfies_isRestriction_iff I, rt_trace_sat_l I, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 支撑、测度与有限幂的所有见证均从所属证书直接构造。 -/
theorem It_local_d.raw_measure_l {ω Γ N T H k κ L n a : M.Domain}
    (owner : Rr_layer_d Kp Γ N T H k) (closed : Rr_closed_d Kp N T H)
    (hN : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Models ZF)
    (hω : M.IsOmega ω) (fs : Fs_read_d ω Γ) (algebra : Sc_algebra_d Γ)
    (w ξ ℓ f : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Domain)
    (hw : Rd_entry_d ω w.val k) (hκ : Rd_entry_d κ ξ.val k)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (hn : M.mem n ω) (support : Fn0_d n L a)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ D U, M.mem D Γ ∧ Ep_space_d κ n D ∧ Sf_ultra_d Γ D U ∧
      Er_measure_d Kp ω κ L N T f.val k a U := by
  let N₀ := smdl_structure_l Kp (R := T) ⟨H, owner.member⟩
  have ext : Rf_ext_d Kp N T := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members (⟨x, hx⟩ : N₀.Domain) ⟨y, hy⟩ (fun z => same z.val z.property))
  obtain ⟨m₀, a₁, hm, fa, graph⟩ := owner.finite_function_l hZF hN.1 (KP.exists_pair (ZF.modelsKP hN)) (KP.exists_union (ZF.modelsKP hN)) hω
    (fs.transitive ω fs.omega_mem) hn (support.mono_target_l (fun x hx => ((length x).mp hx).1))
  let m : N₀.Domain := ⟨m₀, owner.injection.1.output_mem_of_pairMember hm⟩
  let a₀ : N₀.Domain := ⟨a₁, fa.mem_l Kp⟩
  have nativeSupport := owner.function_range_l hZF hN.1 m ℓ a₀ hm support
    (fun x hx => ((length x).mp hx).2) fa graph
  obtain ⟨D, hD, space⟩ := fs.spaces κ n (owner.injection.1.input_mem_of_pairMember hκ) hn
  obtain ⟨A, hA, product⟩ := algebra.product n κ (fs.transitive ω fs.omega_mem n hn)
    (owner.injection.1.input_mem_of_pairMember hκ)
  obtain ⟨d, hd, hDd⟩ := owner.injection.1.2.2 D hD
  have nativeSpace := owner.function_space_l hZF ext closed m ξ (⟨d, hd⟩ : N₀.Domain) hm hκ hDd hA product space
  have actual := loc.read_l Kp _ (kp_pair_l (ZF.modelsKP hN)) hN.1 w ξ ℓ f
  have hn' : N₀.mem m w := (owner.predecessors ω w.val hw m.val).mpr ⟨n, hn, hm⟩
  obtain ⟨u, hau⟩ := actual.measures.total m a₀ hn' nativeSupport
  have measure := actual.measures.at_l hN.1 hau nativeSupport nativeSpace
  obtain ⟨t, P, U, ht, _, _, ultra, spec⟩ := owner.measure_l Kp hZF (ZF.modelsKP hN) ⟨d, hd⟩ u hDd (ZF.exists_powerSet hN ⟨d, hd⟩) measure
  exact ⟨D, U, hD, space, ultra, n, m.val, a₀.val, u.val, D, t, hn, support, hm,
    fa, graph, (rf_val_native_l Kp _ hN.1 a₀ u f).mpr hau, space, ht, spec⟩

/-- 给定原支撑码及其实际测度时，表中坐标迹读取的恰好是同一个原对象。 -/
theorem Er_measure_d.trace_l {ω Γ N T H k κ L n a D U : M.Domain}
    (owner : Rr_layer_d Kp Γ N T H k)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩))
    (f b u : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Domain)
    (function : ∀ b u v, Rd_entry_d b u f → Rd_entry_d b v f → u = v)
    (code : Rr_finite_d Kp ω L N T k a b.val) (value : Rd_entry_d b u f)
    (fa : Fn0_d n L a) (space : Ep_space_d κ n D)
    (h : Er_measure_d Kp ω κ L N T f.val k a U) :
    ∃ t, M.IsRestrictionOf Kp t k D ∧
      ∀ A, M.mem A U ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d Kp D t T B A := by
  obtain ⟨n', m, b', u', D', t, hn, fa', hnm, fn, graph, value', space', ht, spec⟩ := h
  have eq := (show Rr_finite_d Kp ω L N T k a b' from ⟨n', m, hn, fa', hnm, fn, graph⟩).unique_l
    hZF owner ext code
  subst b'
  have eq : u' = u.val := congrArg Subtype.val (function b ⟨u', (value'.bounds_l Kp).2.1⟩ u
    ((rf_val_native_l Kp _ ext b _ f).mp value') value)
  subst u'
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  have eq := hZF.1.eq_of_same_members D' D (fun s => (space' s).trans (space s).symm)
  subst D'
  exact ⟨t, ht, spec⟩

/-- 支撑码及原测度唯一，限制坐标与全部成员迹也随之唯一。 -/
theorem Er_measure_d.unique_l {ω Γ N T H k κ L a U V : M.Domain}
    (owner : Rr_layer_d Kp Γ N T H k)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩))
    (f : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Domain)
    (function : ∀ b u v, Rd_entry_d b u f → Rd_entry_d b v f → u = v)
    (h : Er_measure_d Kp ω κ L N T f.val k a U)
    (g : Er_measure_d Kp ω κ L N T f.val k a V) : U = V := by
  obtain ⟨n, m, b, u, D, t, hn, fa, hnm, fn, graph, value, space, ht, spec⟩ := h
  let b' : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Domain := ⟨b, fn.mem_l Kp⟩
  let u' : (smdl_structure_l Kp (R := T) ⟨H, owner.member⟩).Domain := ⟨u, (value.bounds_l Kp).2.1⟩
  obtain ⟨t', ht', spec'⟩ := g.trace_l hZF owner ext f b' u' function
    ⟨n, m, hn, fa, hnm, fn, graph⟩ ((rf_val_native_l Kp _ ext b' u' f).mp value) fa space
  have eq := ht'.1.eq_of_pairMember_iff hZF.1 ht.1 (fun s x => (ht'.2 s x).trans (ht.2 s x).symm)
  subst t'
  exact hZF.1.eq_of_same_members U V (fun A => (spec A).trans (spec' A).symm)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系所属扩展器的实际支撑协调律

支撑值可以位于高层，坐标重排和 κ 值函数仍由共同低层完整实现。
内部逆像集合先以子集闭包回收到同一层，再用有界公式识别实际逆像；
两端测度成员资格按原测度读取，得到同一实际测度图的协调律。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_coherent_l {ω Γ N T H k κ L F : M.Domain}
    (owner : Rr_layer_d I Γ N T H k) (closed : Rr_closed_d I N T H)
    (hN : (smdl_structure_l I (R := T) ⟨H, owner.member⟩).Models ZF)
    (fs : Fs_read_d ω Γ) (algebra : Sc_algebra_d Γ)
    (w ξ ℓ f : (smdl_structure_l I (R := T) ⟨H, owner.member⟩).Domain)
    (hw : Rd_entry_d ω w.val k) (hκ : Rd_entry_d κ ξ.val k)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (table : ∀ a U, Rd_entry_d a U F ↔ Er_measure_d I ω κ L N T f.val k a U) :
    Ec_source_d I ω κ L Γ F := by
  let N₀ := smdl_structure_l I (R := T) ⟨H, owner.member⟩
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members (⟨x, hx⟩ : N₀.Domain) ⟨y, hy⟩ (fun z => same z.val z.property))
  have actual := loc.read_l I _ (kp_pair_l (ZF.modelsKP hN)) hN.1 w ξ ℓ f
  have low n (hn : M.mem n ω) := fs.transitive ω fs.omega_mem n hn
  have space (n : M.Domain) (hn : M.mem n ω) (m : N₀.Domain) (hnm : Rd_entry_d n m.val k)
      {D : M.Domain} (spec : Ep_space_d κ n D) :
      ∃ d : N₀.Domain, Rd_entry_d D d.val k ∧ ∀ s : N₀.Domain, N₀.mem s d ↔ Fn0_d m ξ s := by
    obtain ⟨D', hD, spec'⟩ := fs.spaces κ n (owner.injection.1.input_mem_of_pairMember hκ) hn
    have eq := hZF.1.eq_of_same_members D' D (fun s => (spec' s).trans (spec s).symm)
    subst D'
    obtain ⟨d, hd, hDd⟩ := owner.injection.1.2.2 D hD
    obtain ⟨P, hP, product⟩ := algebra.product n κ (low n hn) (owner.injection.1.input_mem_of_pairMember hκ)
    exact ⟨⟨d, hd⟩, hDd, owner.function_space_l hZF ext closed m ξ ⟨d, hd⟩ hnm hκ hDd hP product spec⟩
  intro m n q a b U V A hm hn hA hq fa ba haV hbU subsets
  obtain ⟨n₁, n₀, a₀, v₀, E, tE, _, fa₁, hnn, fna, ga, av, sE, htE, specV⟩ := (table a V).mp haV
  have eq := fa₁.domain_eq_l hZF.1 fa
  subst n₁
  obtain ⟨m₁, m₀, b₀, u₀, D, tD, _, fb₁, hmm, fnb, gb, bu, sD, htD, specU⟩ := (table b U).mp hbU
  have eq := fb₁.domain_eq_l hZF.1 ba.1
  subst m₁
  let m' : N₀.Domain := ⟨m₀, owner.injection.1.output_mem_of_pairMember hmm⟩
  let n' : N₀.Domain := ⟨n₀, owner.injection.1.output_mem_of_pairMember hnn⟩
  let a' : N₀.Domain := ⟨a₀, fna.mem_l I⟩
  let b' : N₀.Domain := ⟨b₀, fnb.mem_l I⟩
  let u' : N₀.Domain := ⟨u₀, (bu.bounds_l I).2.1⟩
  let v' : N₀.Domain := ⟨v₀, (av.bounds_l I).2.1⟩
  have hqΓ := fs.functions m n q hm (fs.transitive n (low n hn)) hq
  obtain ⟨q₀, hq₀, hqq⟩ := owner.injection.1.2.2 q hqΓ
  let q' : N₀.Domain := ⟨q₀, hq₀⟩
  have fq := (rr_realize_function_l I hZF.1 owner.transitive ⟨H, owner.member⟩ ext
    owner.injection owner.predecessors n' m' q' hnn hmm hqq hq).1
  have fa' := owner.function_range_l hZF hN.1 n' ℓ a' hnn fa
    (fun x hx => ((length x).mp hx).2) fna ga
  have fb' := owner.function_range_l hZF hN.1 m' ℓ b' hmm ba.1
    (fun x hx => ((length x).mp hx).2) fnb gb
  have ba' := (owner.composition_l hZF hN.1 m' n' ℓ q' a' b' hmm hnn hqq length ba.1 fb' ga gb).mp ba
  obtain ⟨d, hDd, nativeD⟩ := space m hm m' hmm sD
  obtain ⟨e, hEe, nativeE⟩ := space n hn n' hnn sE
  obtain ⟨aA, haA, hAa⟩ := owner.injection.1.2.2 A hA
  let A' : N₀.Domain := ⟨aA, haA⟩
  have subAD : M.MemberSubset A D := fun s hs => (sD s).mpr (subsets s hs)
  have subsets' (s : N₀.Domain) (hs : N₀.mem s A') : Fn0_d m' ξ s := by
    obtain ⟨x, hx, hxs⟩ := (owner.predecessors A aA hAa s.val).mp hs
    exact (nativeD s).mp ((owner.predecessors D d.val hDd s.val).mpr ⟨x, subAD x hx, hxs⟩)
  have av' := (rf_val_native_l I _ hN.1 a' v' f).mp av
  have bu' := (rf_val_native_l I _ hN.1 b' u' f).mp bu
  obtain ⟨Z, pull, same⟩ := actual.coherent m' n' q' a' b' u' v' A'
    ((owner.predecessors ω w.val hw m'.val).mpr ⟨m, hm, hmm⟩)
    ((owner.predecessors ω w.val hw n'.val).mpr ⟨n, hn, hnn⟩) fq fa' ba' av' bu' subsets'
  -- 内部逆像为 e 的子集，完整低层回收得到同一实际集合 B。
  obtain ⟨B, hB, hBZ, subBE⟩ := rr_capture_l I closed owner.transitive owner.injection
    owner.image owner.predecessors hEe Z.property
    (fun x hx hxZ => (nativeE ⟨x, hx⟩).mpr ((pull ⟨x, hx⟩).mp hxZ).1)
  let nc : Nonempty {x // M.mem x Γ} := ⟨⟨ω, fs.omega_mem⟩⟩
  let ψ : Formula 1 7 := Formula.forallMem .newest
    (.iff (.mem .newest (.bound 2)) (Formula.existsMem (.bound 3)
      (cp0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)))
  let η : Env N₀ 7 := ⟨Fin.cases e (Fin.cases Z (Fin.cases A' (Fin.cases q'
    (Fin.cases ξ (Fin.cases n' (fun _ => m')))))), fun _ => w⟩
  have native : Formula.satisfies η ψ := by
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, cp0_sat_l hN.1]
    exact fun s hs => (pull s).trans (and_iff_right ((nativeE s).mp hs))
  have read := (rr_realize_delta_l I owner.transitive nc ⟨H, owner.member⟩ owner.injection owner.predecessors
    ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (.existsMem _ (cp0_delta_l ..))))
    (⟨Fin.cases ⟨E, owner.injection.1.input_mem_of_pairMember hEe⟩ (Fin.cases ⟨B, hB⟩
      (Fin.cases ⟨A, hA⟩ (Fin.cases ⟨q, hqΓ⟩ (Fin.cases ⟨κ, owner.injection.1.input_mem_of_pairMember hκ⟩
        (Fin.cases ⟨n, low n hn⟩ (fun _ => ⟨m, low m hm⟩)))))), fun _ => ⟨ω, fs.omega_mem⟩⟩ :
      Env (rt_model_l Γ nc) 7) η
    (Fin.cases hEe (Fin.cases hBZ (Fin.cases hAa (Fin.cases hqq (Fin.cases hκ (Fin.cases hnn (fun _ => hmm)))))))).mpr native
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, cp0_sat_l hZF.1] at read
  change ∀ s, M.mem s E → (M.mem s B ↔ ∃ t, M.mem t A ∧ Cp0_d m n κ q s t) at read
  have image : Es_pull_d m n κ q A B := fun s =>
    ⟨fun hs => ⟨(sE s).mp (subBE s hs), (read s (subBE s hs)).mp hs⟩,
      fun ⟨hs, ht⟩ => (read s ((sE s).mpr hs)).mpr ht⟩
  have measureU := actual.measures.at_l hN.1 bu' fb' nativeD
  have measureV := actual.measures.at_l hN.1 av' fa' nativeE
  have onto {D d t} (hd : Rd_entry_d D d k) (ht : M.IsRestrictionOf I t k D)
      x (_ : M.mem x N) (hx : Rd_entry_d x d T) : ∃ s, M.mem s D ∧ Rd_entry_d s x t := by
    obtain ⟨s, hs, hsx⟩ := (owner.predecessors D d hd x).mp hx
    exact ⟨s, hs, (ht.2 s x).mpr ⟨hs, hsx⟩⟩
  have subZ : N₀.MemberSubset Z e := fun s hs => (nativeE s).mpr ((pull s).mp hs).1
  have subA : N₀.MemberSubset A' d := fun s hs => (nativeD s).mpr (subsets' s hs)
  have readV := rt_measure_read_l I ⟨H, owner.member⟩ hN.1 e v' Z
    (htE.isSetFunctionFromTo owner.injection.1 (owner.transitive E (owner.injection.1.input_mem_of_pairMember hEe)))
    (onto hEe htE) subZ (owner.trace_l I hBZ htE subBE) measureV.1.1 specV
  have readU := rt_measure_read_l I ⟨H, owner.member⟩ hN.1 d u' A'
    (htD.isSetFunctionFromTo owner.injection.1 (owner.transitive D (owner.injection.1.input_mem_of_pairMember hDd)))
    (onto hDd htD) subA (owner.trace_l I hAa htD subAD) measureU.1.1 specU
  exact ⟨B, image, readV.trans (same.trans readU.symm)⟩

/-- 所有背景内部有限支撑同时装配成实际测度图，供原定向系统直接使用。 -/
theorem It_local_d.raw_family_l {ω Γ N T H k κ : M.Domain}
    (owner : Rr_layer_d I Γ N T H k) (closed : Rr_closed_d I N T H)
    (hN : (smdl_structure_l I (R := T) ⟨H, owner.member⟩).Models ZF)
    (hω : M.IsOmega ω) (fs : Fs_read_d ω Γ) (algebra : Sc_algebra_d Γ)
    (w ξ ℓ f : (smdl_structure_l I (R := T) ⟨H, owner.member⟩).Domain)
    (hw : Rd_entry_d ω w.val k) (hκ : Rd_entry_d κ ξ.val k)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val) :
    ∃ L F, (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      Em_source_d ω κ L Γ F ∧ Ec_source_d I ω κ L Γ F ∧
      ∀ a U, Rd_entry_d a U F ↔ Er_measure_d I ω κ L N T f.val k a U := by
  let η : Env M 2 := ⟨Fin.cases ℓ.val (fun _ => T), fun _ => N⟩
  let ψ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨L, length⟩ := ZF.separation_exists_d hZF ψ η N
  have length x : M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T :=
    (length x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨J, indices⟩ := ZF.fseq_space_exists_l I hZF hω L
  let N₀ := smdl_structure_l I (R := T) ⟨H, owner.member⟩
  have actual := loc.read_l I _ (kp_pair_l (ZF.modelsKP hN)) hN.1 w ξ ℓ f
  let θ : Env M 7 := ⟨Fin.cases k (Fin.cases f.val (Fin.cases T (Fin.cases N
    (Fin.cases L (Fin.cases κ (fun _ => ω)))))), fun _ => ω⟩
  let φ : BinarySchema 7 := {
    body := er_measure_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a U : φ.denote θ a U ↔ Er_measure_d I ω κ L N T f.val k a U :=
    er_measure_sat_l I hZF.1 ..
  have total a (ha : M.mem a J) : ∃ U, φ.denote θ a U := by
    obtain ⟨n, hn, fa⟩ := (indices a).mp ha
    obtain ⟨_, U, _, _, _, hU⟩ := loc.raw_measure_l hZF owner closed hN hω fs algebra w ξ ℓ f hw hκ
      length hn (fn0_of_function_l (ZF.modelsKP hZF) fa)
    exact ⟨U, (sat a U).mpr hU⟩
  have unique a (_ : M.mem a J) U V (hu : φ.denote θ a U) (hv : φ.denote θ a V) : U = V :=
    ((sat a U).mp hu).unique_l hZF owner hN.1 f actual.measures.function ((sat a V).mp hv)
  obtain ⟨Q, hQ⟩ := ZF.exists_functionalImageOn hZF φ θ J total unique
  obtain ⟨F, ff, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ θ total unique
    (fun a U ha hu => (hQ U).mpr ⟨a, ha, hu⟩)
  have graph a U : Rd_entry_d a U F ↔ Er_measure_d I ω κ L N T f.val k a U := by
    apply (spec a U).trans
    constructor
    · exact fun h => (sat a U).mp h.2
    · intro h
      have code := h
      obtain ⟨n, _, _, _, _, _, hn, fa, _⟩ := code
      exact ⟨(indices a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fa⟩, (sat a U).mpr h⟩
  refine ⟨L, F, length, ⟨?_, fun a U V => ff.1.2 a U V, ?_⟩,
    loc.raw_coherent_l hZF owner closed hN fs algebra w ξ ℓ f hw hκ length graph, graph⟩
  · intro n a hn fa
    exact (ff.2.2 a ((indices a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fa⟩)).imp fun _ h => h.2
  · intro a U ha
    have h := (graph a U).mp ha
    have code := h
    obtain ⟨n, _, _, _, _, _, hn, fa, _⟩ := code
    obtain ⟨D, V, _, space, measure, hv⟩ := loc.raw_measure_l hZF owner closed hN hω fs algebra w ξ ℓ f hw hκ length hn fa
    exact ⟨n, D, hn, fa, space,
      hv.unique_l hZF owner hN.1 f actual.measures.function h ▸ measure⟩

end YesMetaZFC.SetTheory.LargeCardinal
