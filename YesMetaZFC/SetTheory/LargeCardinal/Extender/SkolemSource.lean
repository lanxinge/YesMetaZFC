import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem

/-! # 实际源中的有限程序与有限赋值空间

任意合法内部程序的指令都由自然数配对得到；有限函数闭性将整张程序图
放入源中。所有空间与界均实际构造，不假设源包含完整的 ω 赋值空间。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.finite_space_l {ω κ K Z S A b : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hA : M.mem A Z) (hb : M.mem b ω) :
    ∃ E, M.mem E Z ∧ M.IsFunctionSpace I E b A := by
  obtain ⟨J, hJZ, hJ⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 A hA
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => A), fun _ => b⟩
  let φ : UnarySchema 2 := { body := fn0_m (.bound 1) (.bound 2) .newest }
  obtain ⟨E, hEZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory
    φ (fn0_delta_l ..) ρ (Fin.cases (source.transitive ω source.omega_mem b hb) (fun _ => hA)) hJZ
  refine ⟨E, hEZ, fun f => (spec f).trans ?_⟩
  have sat : φ.denote ρ f ↔ Fn0_d b A f := fn0_sat_l hZF.1 ..
  exact (and_congr_right fun _ => sat).trans ⟨fun h => fn0_function_l (ZF.modelsKP hZF) h.2,
    fun hf => ⟨(hJ f).mpr ⟨b, hb, hf⟩, fn0_of_function_l (ZF.modelsKP hZF) hf⟩⟩

theorem Ep_source_d.program_l {ω κ K Z S n F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hF : Sfm_d I ω n F) :
    M.mem F Z ∧ ∃ b L, M.mem L Z ∧ Fb_program_d (ZF.modelsKP hZF) ω b n L F := by
  have pair {p a b} (h : KPair_d M p a b) (ha : M.mem a Z) (hb : M.mem b Z) : M.mem p Z := by
    obtain ⟨q, hq, eq⟩ := source.kpair_l hZF ha hb
    exact kpair_unique_l M hZF.1 eq h ▸ hq
  have op {k c i j} (h : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c Z := by
    obtain ⟨a, o, ho, ha, hc⟩ := h
    exact pair hc (source.transitive ω source.omega_mem o (num_mem_l hZF.1 source.omega ho))
      (pair ha (source.transitive ω source.omega_mem i hi) (source.transitive ω source.omega_mem j hj))
  have row r c (hc : Rd_entry_d r c F) : M.mem c Z := by
    have hr := source.omega.transitive (ZF.modelsKP hZF) n hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
    rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact op hs hi hj
    · exact op hs hi hj
    · exact op hs (source.omega.transitive (ZF.modelsKP hZF) r hr i hi) (source.omega.transitive (ZF.modelsKP hZF) r hr j hj)
    · exact op hs hi (source.omega.transitive (ZF.modelsKP hZF) r hr j hj)
  have fn : M.IsSetFunctionFromTo I F n Z := ⟨hF.2.1.2.1, hF.2.1.2.2, fun r hr =>
    ((hF.2.1.2.2 r).mp hr).imp fun c hc => ⟨row r c hc, hc⟩⟩
  obtain ⟨c, hc⟩ := source.code
  have hFZ := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
    (fun _ h => h) hF.1 (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨_, L, hLZ, hfL⟩ := source.function_l hZF
    hFZ (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF source.omega hF
  exact ⟨hFZ, b, L, hLZ, fb_program_of_l (ZF.modelsKP hZF) hF hb bound hfL⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内实际存在的有限真值表

对程序行作内部强归纳。原子、布尔步和有限赋值的量词投影均由源内 Δ₀
分离给出；有限函数闭性随后收集整张表。无需源包含赋值空间的完整幂集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.finite_evaluation_l {ω κ K Z S b A R E n L F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hA : M.mem A Z) (hR : M.mem R Z) (hEZ : M.mem E Z)
    (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F) (hE : M.IsFunctionSpace I E b A) :
    ∃ C H, M.mem C Z ∧ M.mem H Z ∧ Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H := by
  have hω := source.omega
  obtain ⟨hF, bound⟩ := program.read_l hZF hω
  obtain ⟨H, hH⟩ := seval_exists_l I hZF A R E F hF.2.1.1
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hH.1.2.1 hH.1.2.2
  have fnH : M.IsSetFunctionFromTo I H n C := ⟨hH.1.2.1, hH.1.2.2, fun r hr =>
    ((hH.1.2.2 r).mp hr).imp fun Y hY => ⟨(hC Y).mpr ⟨r, hY⟩, hY⟩⟩
  have row_sub r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp (fnH.input_mem_of_pairMember hY)
    exact fun f hf => ((seval_row_l I hZF hF hH hc hY f).mp hf).1
  obtain ⟨c₀, model⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases H (fun _ => Z), fun _ => H⟩
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (rd_entry0_m (.bound 1) .newest (.bound 2)) (.mem .newest (.bound 3))) }
  have sat r : φ.denote ρ r ↔ ∀ Y, Rd_entry_d r Y H → M.mem Y Z := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have rows r (hr : M.mem r n) : ∀ Y, Rd_entry_d r Y H → M.mem Y Z := by
    apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr)
    intro r hr ih
    apply (sat r).mpr
    intro Y hrY
    obtain ⟨c, hrc⟩ := (hF.2.1.2.2 r).mp hr
    have finish {p i j} (k : Fin 4) (hs : Sop_d I k.val c i j) (ψ : UnarySchema p)
        (hd : ψ.body.IsDelta0) (η : Env M p) (hη : ∀ i, M.mem (η.bound i) Z)
        (read : ∀ f, M.mem f E → (ψ.denote η f ↔ Sarg_d I k.val A R H f i j)) : M.mem Y Z := by
      obtain ⟨D, hDZ, spec⟩ := sc_separate_source_l I hZF hω source.transitive model source.theory ψ hd η hη hEZ
      have eq : D = Y := hZF.1.eq_of_same_members D Y (fun f => (spec f).trans
        ((and_congr_right fun hf => (read f hf).trans (snode_decode_l I (ZF.modelsKP hZF) k hs).symm).trans
          (seval_row_l I hZF hF hH hrc hrY f).symm))
      exact eq ▸ hDZ
    rcases hF.2.2 r c hrc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · let η : Env M 4 := ⟨Fin.cases i (Fin.cases j (Fin.cases A (fun _ => R))), fun _ => A⟩
      let ψ : UnarySchema 4 := {
        body := fv_arg_m 0 (.bound 3) (.bound 3) (.bound 4) (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2) }
      apply finish 0 hs ψ (fv_arg_delta_l 0 (.bound 3) (.bound 3) (.bound 4)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)) η
        (Fin.cases (source.transitive ω source.omega_mem i hi)
          (Fin.cases (source.transitive ω source.omega_mem j hj) (Fin.cases hA (fun _ => hR))))
      intro f hf
      exact (fv_arg_sat_l hZF.1 0 (η.push f) (.bound 3) (.bound 3) (.bound 4)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)).trans (fv_arg_l (ZF.modelsKP hZF) hE hf
        (bound.operands_l I hrc hs).1 (fn0_of_function_l (ZF.modelsKP hZF) fnH) row_sub 0)
    · let η : Env M 3 := ⟨Fin.cases i (Fin.cases j (fun _ => A)), fun _ => A⟩
      let ψ : UnarySchema 3 := {
        body := fv_arg_m 1 (.bound 3) (.bound 3) (.bound 3) (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2) }
      apply finish 1 hs ψ (fv_arg_delta_l 1 (.bound 3) (.bound 3) (.bound 3)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)) η
        (Fin.cases (source.transitive ω source.omega_mem i hi)
          (Fin.cases (source.transitive ω source.omega_mem j hj) (fun _ => hA)))
      intro f hf
      exact (fv_arg_sat_l hZF.1 1 (η.push f) (.bound 3) (.bound 3) (.bound 3)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)).trans (fv_arg_l (ZF.modelsKP hZF) hE hf
        (bound.operands_l I hrc hs).1 (fn0_of_function_l (ZF.modelsKP hZF) fnH) row_sub 1)
    · obtain ⟨U, hiU⟩ := (hH.1.2.2 i).mp (hF.2.1.1.transitive r hr i hi)
      obtain ⟨V, hjV⟩ := (hH.1.2.2 j).mp (hF.2.1.1.transitive r hr j hj)
      let η : Env M 2 := ⟨Fin.cases U (fun _ => V), fun _ => U⟩
      let ψ : UnarySchema 2 := { body := .neg (.disj (.mem .newest (.bound 1)) (.mem .newest (.bound 2))) }
      apply finish 2 hs ψ (.neg (.disj (.mem _ _) (.mem _ _))) η
        (Fin.cases ((sat i).mp (ih i hi) U hiU) (fun _ => (sat j).mp (ih j hj) V hjV))
      intro f _
      simp only [ψ, UnarySchema.denote, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff]
      change (¬ (M.mem f U ∨ M.mem f V)) ↔ Sarg_d I 2 A R H f i j
      exact ⟨fun h => ⟨U, V, hiU, hjV, h⟩, fun ⟨U', V', hiU', hjV', h⟩ =>
        fnH.1.2 i U' U hiU' hiU ▸ fnH.1.2 j V' V hjV' hjV ▸ h⟩
    · obtain ⟨V, hjV⟩ := (hH.1.2.2 j).mp (hF.2.1.1.transitive r hr j hj)
      let η : Env M 5 := ⟨Fin.cases b (Fin.cases A (Fin.cases E (Fin.cases i (fun _ => V)))), fun _ => A⟩
      let ψ : UnarySchema 5 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
        (.conj (se_update0_m (.bound 3) (.bound 4) (.bound 2) (.bound 6) (.bound 1) .newest) (.mem .newest (.bound 7)))) }
      have read f : ψ.denote η f ↔ ∃ x, M.mem x A ∧ ∃ g, M.mem g E ∧ Se_update0_d b A f i x g ∧ M.mem g V := by
        simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
          se_update0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
      apply finish 3 hs ψ (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _)))) η
        (Fin.cases (source.transitive ω source.omega_mem b program.1) (Fin.cases hA (Fin.cases hEZ
          (Fin.cases (source.transitive ω source.omega_mem i hi) (fun _ => (sat j).mp (ih j hj) V hjV)))))
      intro f hf
      have update x (hx : M.mem x A) (g : M.Domain) := se_update0_l (g := g) (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((hE f).mp hf))
        (bound.operands_l I hrc hs).1 hx
      refine (read f).trans ⟨fun ⟨x, hx, g, _, hg, h⟩ => ⟨V, hjV, x, g, hx, (update x hx g).mp hg, h⟩, ?_⟩
      rintro ⟨V', hjV', x, g, hx, hg, h⟩
      have eq := fnH.1.2 j V' V hjV' hjV
      subst V'
      exact ⟨x, hx, g, row_sub j V hjV g h, (update x hx g).mpr hg, h⟩
  have fnZ := (fn0_of_function_l (ZF.modelsKP hZF) fnH).retarget_l
    (fun r Y hY => rows r (fnH.input_mem_of_pairMember hY) Y hY)
  have hHZ := sc_finite_function_l (ZF.modelsKP hZF) hω source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
    (fun _ h => h) hF.1 fnZ
  obtain ⟨_, C', hC'Z, fn'⟩ := source.function_l hZF hHZ fnZ
  exact ⟨C', H, hC'Z, hHZ, fv_eval_of_l hZF hω program hE hH fn'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限代表列的源内转置矩阵

有限代表列本身属于源。两次取坐标包络给出所有函数值的共同源内界，
有界统一化遂收集逐点有限赋值，且逐项保持原代表的实际求值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.matrix_l {ω κ K X R D b G : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hb : M.mem b ω) (hD : M.mem D X)
    (fg : Fn0_d b X G) (reps : ∀ i f, Rd_entry_d i f G → Fn0_d D X f) :
    ∃ B E V, M.mem B X ∧ M.mem E X ∧ M.mem V X ∧ M.IsFunctionSpace I E b B ∧ Fn0_d D E V ∧
      ∀ v t i f x, Rd_entry_d v t V → Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
  obtain ⟨c, code⟩ := source.code
  have hG := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
    (fun _ h => h) hb fg
  obtain ⟨C, hC, functions⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hG
  obtain ⟨U, hU, union⟩ := (source.algebra_l (ZF.modelsKP hZF)).union C hC
  obtain ⟨B, hB, values⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hU
  have bounded v f x (hf : M.mem f C) (hvx : Rd_entry_d v x f) : M.mem x B := by
    obtain ⟨p, pair, hp⟩ := hvx
    exact (values v x ⟨p, pair, (union p).mpr ⟨f, hf, hp⟩⟩).2
  obtain ⟨E, hE, space⟩ := source.finite_space_l hZF hB hb
  have column v (hv : M.mem v D) : ∃ t, M.mem t E ∧
      ∀ i f x, Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
    let ρ : Env M 3 := ⟨Fin.cases G (Fin.cases C (fun _ => v)), fun _ => v⟩
    let φ : BinarySchema 3 := { body := Formula.existsMem (.bound 3) (.conj
      (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 5) (.bound 1) .newest)) }
    have sat i x : φ.denote ρ i x ↔ ∃ f, M.mem f C ∧ Rd_entry_d i f G ∧ Rd_entry_d v x f := by
      simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
    obtain ⟨t, _, ft, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
      (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
      ρ (Fin.cases hG (Fin.cases hC (fun _ => source.transitive D hD v hv)))
      (source.transitive ω source.omega_mem b hb) hB (fun i hi => by
        obtain ⟨f, _, hif⟩ := fg.2.1 i hi
        obtain ⟨x, _, hvx⟩ := (reps i f hif).2.1 v hv
        exact ⟨x, bounded v f x (functions i f hif).2 hvx,
          (sat i x).mpr ⟨f, (functions i f hif).2, hif, hvx⟩⟩)
    have read i f x (hif : Rd_entry_d i f G) (hix : Rd_entry_d i x t) : Rd_entry_d v x f := by
      obtain ⟨f', _, hif', hvx⟩ := (sat i x).mp (select i x hix)
      exact (fn0_function_l (ZF.modelsKP hZF) fg).1.2 i f' f hif' hif ▸ hvx
    refine ⟨t, (space t).mpr (fn0_function_l (ZF.modelsKP hZF) ft), fun i f x hif => ⟨read i f x hif, ?_⟩⟩
    intro hvx
    obtain ⟨y, _, hiy⟩ := ft.2.1 i (fg.bound_l hif).1
    exact (fn0_function_l (ZF.modelsKP hZF) (reps i f hif)).1.2 v y x (read i f y hif hiy) hvx ▸ hiy
  let ρ : Env M 4 := ⟨Fin.cases G (Fin.cases C (Fin.cases B (fun _ => b))), fun _ => b⟩
  let φ : BinarySchema 4 := { body := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 4)
    (Formula.forallMem (.bound 6) (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
      (.iff (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m (.bound 4) .newest (.bound 1)))))) }
  have sat v t : φ.denote ρ v t ↔ ∀ i, M.mem i b → ∀ f, M.mem f C → ∀ x, M.mem x B →
      Rd_entry_d i f G → (Rd_entry_d i x t ↔ Rd_entry_d v x f) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨V, hV, fv, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    ρ (Fin.cases hG (Fin.cases hC (Fin.cases hB (fun _ => source.transitive ω source.omega_mem b hb))))
    hD hE (fun v hv => by
      obtain ⟨t, ht, point⟩ := column v hv
      exact ⟨t, ht, (sat v t).mpr fun i _ f _ x _ hif => point i f x hif⟩)
  refine ⟨B, E, V, hB, hE, hV, space, fv, fun v t i f x hvt hif => ?_⟩
  have point := (sat v t).mp (select v t hvt) i (fg.bound_l hif).1 f (functions i f hif).2 x
  have ft := fn0_of_function_l (ZF.modelsKP hZF) ((space t).mp (fv.bound_l hvt).2)
  exact ⟨fun hix => (point (ft.bound_l hix).2 hif).mp hix,
    fun hvx => (point (bounded v f x (functions i f hif).2 hvx) hif).mpr hvx⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Skolem 见证的源内有限证书

每个原见证所需的程序、有限赋值和真值表都实际属于源。反向读取只用
有界矩阵绝对性，所以源中的见证检验覆盖全部背景内部公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fw_source_d (hKP : M.Models KP) (Z ω A R J u a i s x : M.Domain) : Prop :=
  ∃ n b l L F E C H t r, M.mem n Z ∧ M.mem b Z ∧ M.mem l Z ∧ M.mem L Z ∧ M.mem F Z ∧
    M.mem E Z ∧ M.mem C Z ∧ M.mem H Z ∧ M.mem t Z ∧ M.mem r Z ∧
      Fw_cert_d hKP ω A R J u a i s x n b l L F E C H t r

theorem fw_relative_sat_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x : M.Domain // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (ω A R J u a i s x : Term d) :
    Formula.satisfies ρ (fw_witness_m ω A R J u a i s x) ↔ Fw_source_d hKP Z
      (ω.eval ρ).val (A.eval ρ).val (R.eval ρ).val (J.eval ρ).val (u.eval ρ).val
      (a.eval ρ).val (i.eval ρ).val (s.eval ρ).val (x.eval ρ).val := by
  have cert {d} (η : Env (rt_model_l Z hz) d) (ω A R J u a i s x n b l L F E C H t r : Term d) :
      Formula.satisfies η (fw_cert_m ω A R J u a i s x n b l L F E C H t r) ↔ Fw_cert_d hKP
        (ω.eval η).val (A.eval η).val (R.eval η).val (J.eval η).val (u.eval η).val (a.eval η).val
        (i.eval η).val (s.eval η).val (x.eval η).val (n.eval η).val (b.eval η).val (l.eval η).val
        (L.eval η).val (F.eval η).val (E.eval η).val (C.eval η).val (H.eval η).val (t.eval η).val (r.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (fw_cert_delta_l ω A R J u a i s x n b l L F E C H t r) η).trans (fw_cert_sat_l hKP ..)
  simp only [fw_witness_m, Formula.satisfies_exists_iff, cert, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨n, b, l, L, F, E, C, H, t, r, h⟩
    exact ⟨n.val, b.val, l.val, L.val, F.val, E.val, C.val, H.val, t.val, r.val,
      n.property, b.property, l.property, L.property, F.property, E.property, C.property, H.property, t.property, r.property, h⟩
  · rintro ⟨n, b, l, L, F, E, C, H, t, r, hn, hb, hl, hL, hF, hE, hC, hH, ht, hr, h⟩
    exact ⟨⟨n, hn⟩, ⟨b, hb⟩, ⟨l, hl⟩, ⟨L, hL⟩, ⟨F, hF⟩, ⟨E, hE⟩, ⟨C, hC⟩, ⟨H, hH⟩, ⟨t, ht⟩, ⟨r, hr⟩, h⟩

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.finite_witness_l {ω κ K Z W c A R J u a i s x : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (hA : M.mem A Z) (hR : M.mem R Z)
    (hm : Smdl_d I c A R) (hJ : Fseq_space_d I ω A J) (hu : M.mem u A) (hi : M.mem i ω) (hx : M.mem x A) :
    Fw_source_d (ZF.modelsKP hZF) Z ω A R J u a i s x ↔ Ssk_wit_d I ω c A u a i s x := by
  constructor
  · rintro ⟨n, b, l, L, F, E, C, H, t, r, _, _, _, _, _, _, _, _, _, _, cert⟩
    exact cert.witness_l hZF source.omega hm hJ hu hi hx
  · rintro ⟨n, f, g, hn, hs, fill, update, A', R', D, l, F, r, hm', code, hD, truth⟩
    obtain ⟨hAeq, hReq⟩ := smdl_unique_l I hm' hm
    subst A'; subst R'
    obtain ⟨hFZ, b, L, hLZ, program⟩ := source.program_l hZF code.2.1
    have bound := (program.read_l hZF source.omega).2
    have sub := source.omega.transitive (ZF.modelsKP hZF) b program.1
    have gf := update.function_l I (fill.function_l I hs hu) hi hx
    obtain ⟨t, res⟩ := ZF.exists_restriction hZF I g b
    have tf := res.isSetFunctionFromTo gf sub
    have agree : Senv_agree_d I b g t := fun v y hv => ((res.2 v y).trans (and_iff_right hv)).symm
    obtain ⟨E, hEZ, hE⟩ := source.finite_space_l hZF hA program.1
    obtain ⟨C, H, hCZ, hHZ, ev⟩ := source.finite_evaluation_l hZF hA hR hEZ program hE
    have htE := (hE t).mpr tf
    have same := ssat_spaces_l I hZF (R := R) code.2.1 bound hD hE sub (fun _ h => h) code.2.2
      ((hD g).mpr gf) htE agree
    exact ⟨n, b, l, L, F, E, C, H, t, r,
      source.transitive ω source.omega_mem n hn, source.transitive ω source.omega_mem b program.1,
      source.transitive ω source.omega_mem l program.2.1, hLZ, hFZ, hEZ, hCZ, hHZ,
      source.transitive E hEZ t htE, source.transitive ω source.omega_mem r
        (source.omega.transitive (ZF.modelsKP hZF) l program.2.1 r code.2.2),
      hn, fn0_of_function_l (ZF.modelsKP hZF) hs, code.1, code.2.2, program,
      (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mpr hE, ev,
      (fw_env_read_l (ZF.modelsKP hZF) sub fill update gf (fn0_of_function_l (ZF.modelsKP hZF) tf)).mpr agree,
      (ev.truth_l hZF source.omega program hE code.2.2).mpr (same.mp truth)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 小壳公式所量化的全部内部代码

源中的代码集与有限参数空间按原公式读取。合法程序和有限函数的实际
源内存在性排除相对量词遗漏背景内部非标准有限对象的可能。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.codes_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w C : Term d)
    (hw : (w.eval ρ).val = ω) : Formula.satisfies ρ (sh_codes_m w C) ↔ Scode_d I ω (C.eval ρ).val := by
  have prog {e} (η : Env (rt_model_l Z hz) e) (w b l L F : Term e) :
      Formula.satisfies η (fb_program_m w b l L F) ↔
        Fb_program_d (ZF.modelsKP hZF) (w.eval η).val (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (fb_program_delta_l w b l L F) η).trans (fb_program_sat_l (ZF.modelsKP hZF) ..)
  have pair {e} (η : Env (rt_model_l Z hz) e) (p a b : Term e) :
      Formula.satisfies η (kpair0_m p a b) ↔ KPair_d M (p.eval η).val (a.eval η).val (b.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (kpair0_delta_l p a b) η).trans (kpair0_sat_l hZF.1 ..)
  simp only [sh_codes_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, prog, pair, Definitional.Term.eval_weaken, hw]
  have cert {a l F r : M.Domain} (h : Sformula_d I ω a l F r) :
      M.mem a Z ∧ ∃ b L, M.mem b Z ∧ M.mem l Z ∧ M.mem L Z ∧ M.mem F Z ∧ M.mem r Z ∧
        Fb_program_d (ZF.modelsKP hZF) ω b l L F := by
    obtain ⟨hF, b, L, hL, program⟩ := source.program_l hZF h.2.1
    have hr := source.transitive ω source.omega_mem r (source.omega.transitive (ZF.modelsKP hZF) l h.2.1.1 r h.2.2)
    obtain ⟨p, hp, eq⟩ := source.kpair_l hZF hF hr
    exact ⟨kpair_unique_l M hZF.1 eq h.1 ▸ hp, b, L,
      source.transitive ω source.omega_mem b program.1,
      source.transitive ω source.omega_mem l program.2.1, hL, hF, hr, program⟩
  constructor
  · intro h a
    constructor
    · intro ha
      obtain ⟨b, l, L, F, r, program, hr, code⟩ := (h ⟨a, source.transitive _ (C.eval ρ).property a ha⟩).mp ha
      exact ⟨l.val, F.val, r.val, code, (program.read_l hZF source.omega).1, hr⟩
    · rintro ⟨l, F, r, code⟩
      obtain ⟨ha, b, L, hb, hl, hL, hF, hr, program⟩ := cert code
      exact (h ⟨a, ha⟩).mpr ⟨⟨b, hb⟩, ⟨l, hl⟩, ⟨L, hL⟩, ⟨F, hF⟩, ⟨r, hr⟩, program, code.2.2, code.1⟩
  · intro h a
    constructor
    · intro ha
      obtain ⟨l, F, r, code⟩ := (h a.val).mp ha
      obtain ⟨_, b, L, hb, hl, hL, hF, hr, program⟩ := cert code
      exact ⟨⟨b, hb⟩, ⟨l, hl⟩, ⟨L, hL⟩, ⟨F, hF⟩, ⟨r, hr⟩, program, code.2.2, code.1⟩
    · rintro ⟨b, l, L, F, r, program, hr, code⟩
      exact (h a.val).mpr ⟨l.val, F.val, r.val, code, (program.read_l hZF source.omega).1, hr⟩

theorem Ep_source_d.sequences_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A J : Term d)
    (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (sh_sequences_m w A J) ↔ Fseq_space_d I ω (A.eval ρ).val (J.eval ρ).val := by
  have fn (η : Env (rt_model_l Z hz) (d+2)) :
      Formula.satisfies η (fn0_m .newest A.weaken.weaken (.bound 1)) ↔
        Fn0_d (η.bound 0).val (A.weaken.weaken.eval η).val (η.bound 1).val := by
    have tr := (rt_model_delta_l source.transitive hz (fn0_delta_l .newest A.weaken.weaken (.bound 1)) η).trans (fn0_sat_l hZF.1 ..)
    cases A <;> exact tr
  simp only [sh_sequences_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn, Definitional.Term.eval_weaken]
  obtain ⟨L, hL, space⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 _ (A.eval ρ).property
  constructor
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, hs⟩ := (h ⟨f, source.transitive _ (J.eval ρ).property f hf⟩).mp hf
      exact ⟨n.val, hw ▸ hn, fn0_function_l (ZF.modelsKP hZF) hs⟩
    · rintro ⟨n, hn, hf⟩
      exact (h ⟨f, source.transitive L hL f ((space f).mpr ⟨n, hn, hf⟩)⟩).mpr
        ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw.symm ▸ hn, fn0_of_function_l (ZF.modelsKP hZF) hf⟩
  · intro h f
    exact (h f.val).trans ⟨fun ⟨n, hn, hf⟩ =>
      ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw.symm ▸ hn, fn0_of_function_l (ZF.modelsKP hZF) hf⟩,
      fun ⟨n, hn, hf⟩ => ⟨n.val, hw ▸ hn, fn0_function_l (ZF.modelsKP hZF) hf⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 模型内小 Skolem 壳的实际初始实例

只要求大小参数是含 ω 的序数。先以它的实际基数代表作闭包估计，再
恢复原序数上的双射；选择图、最小壳和双射图全部属于正则 Hχ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem sh_source_of_h_l (hZFC : M.Models ZFC) {ω χ Z : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z) (hωZ : M.mem ω Z) :
    Sh_source_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) ω Z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := ZF.h_transitive_l I hZF hZ
  obtain ⟨K₀, hK₀, finite⟩ := ZFC.h_fseq_l hZFC hω hχ hωχ hZ hωZ
  obtain ⟨W, source⟩ := ep_source_of_h_l hZFC hω (fun _ h => h) hχ hωχ hZ hωZ hωZ hK₀ finite
  intro c A R U κ f hAZ _ _ hκZ _ hm hκ hωκ hUA hf
  obtain ⟨u, C, J, T, D, K, N, g, skolem, hull, hg⟩ := ssk_hull_enum_l I hZFC hω hκ hωκ hm hUA hf
  have hC : M.mem C Z := by
    apply ZFC.h_small_closed_l I hZFC hω hχ hωχ hZ ?_ hωχ (scode_countable_l I hZF hω skolem.codes)
    intro a ha
    obtain ⟨n, F, r, code, program, hr⟩ := (skolem.codes a).mp ha
    obtain ⟨hF, _⟩ := source.program_l hZF program
    have hrZ := trans ω hωZ r (hω.transitive (ZF.modelsKP hZF) n program.1 r hr)
    obtain ⟨p, hp, eq⟩ := source.kpair_l hZF hF hrZ
    exact kpair_unique_l M hZF.1 eq code ▸ hp
  obtain ⟨J', hJ', seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 A hAZ
  have hJ : M.mem J Z := hZF.1.eq_of_same_members J' J (fun s => (seq s).trans (skolem.params s).symm) ▸ hJ'
  have hT := ZFC.h_product_l hZFC hω hχ hωχ hZ hC hωZ skolem.labels
  have hD := ZFC.h_product_l hZFC hω hχ hωχ hZ hT hJ skolem.domain
  have hK := ZFC.h_function_l hZFC hω hχ hωχ hZ hD (skolem.graph.mono_target_l I (trans A hAZ))
  have hN := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hZ hAZ N hull.2.1
  exact ⟨u, C, J, T, D, K, N, g, trans A hAZ u skolem.point, hC, hJ, hT, hD, hK, hN,
    ZFC.h_function_l hZFC hω hχ hωχ hZ hκZ (hg.1.1.mono_target_l I (trans N hN)),
    skolem, ⟨hull.1, hull.2.1, hull.2.2.1, fun B _ hUB _ => hull.2.2.2 B hUB⟩, hg⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内 Skolem 选择图与闭包的完整读取 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sh_closed_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (ω A J T D K B : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ).val (A.eval ρ).val (J.eval ρ).val)
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val)
    (hB : M.MemberSubset (B.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_closed_m ω A J T D K B) ↔
      Fc_closed_d (kp_pair_l hKP) (ω.eval ρ).val (T.eval ρ).val (K.eval ρ).val (B.eval ρ).val := by
  have read := sh_closed_sat_l hKP (image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val ρ) ω A J T D K B
  simp only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] at read
  exact (rt_model_delta_l hZ hz (sh_closed_delta_l ω A J T D K B) ρ).trans (read hJ hD hK hB)

theorem sh_hull_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (ω A J T D K U N : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ).val (A.eval ρ).val (J.eval ρ).val)
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_hull_m ω A J T D K U N) ↔
      Sh_hull_d hKP Z (ω.eval ρ).val (A.eval ρ).val (T.eval ρ).val (K.eval ρ).val (U.eval ρ).val (N.eval ρ).val := by
  have sub {e} (η : Env (rt_model_l Z hz) e) (A B : Term e) : Formula.satisfies η (Formula.subset A B) ↔
      M.MemberSubset (A.eval η).val (B.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset,
      eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (.atom ..) η).trans (Formula.satisfies_subset_iff (ℳ := M) (image_env_l Subtype.val η) A B)
  have closed (B : (rt_model_l Z hz).Domain) (hB : M.MemberSubset B.val (A.eval ρ).val) :
      Formula.satisfies (ρ.push B) (sh_closed_m ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest) ↔
        Fc_closed_d (kp_pair_l hKP) (ω.eval ρ).val (T.eval ρ).val (K.eval ρ).val B.val := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      sh_closed_relative_l hKP hZ hz (ρ.push B) ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest
        (by simpa only [Definitional.Term.eval_weaken] using hJ)
        (by simpa only [Definitional.Term.eval_weaken] using hD)
        (by simpa only [Definitional.Term.eval_weaken] using hK)
        (by simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using hB)
  simp only [sh_hull_m, Formula.satisfies_conj_iff, sub, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hU, hN, hc, minimal⟩
    refine ⟨hU, hN, (sh_closed_relative_l hKP hZ hz ρ ω A J T D K N hJ hD hK hN).mp hc, ?_⟩
    intro B hB hUB hBA hc
    exact minimal ⟨B, hB⟩ hUB hBA ((closed ⟨B, hB⟩ hBA).mpr hc)
  · rintro ⟨hU, hN, hc, minimal⟩
    refine ⟨hU, hN, (sh_closed_relative_l hKP hZ hz ρ ω A J T D K N hJ hD hK hN).mpr hc, ?_⟩
    intro B hUB hBA hc
    exact minimal B.val B.property hUB hBA ((closed B hBA).mp hc)

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.select_sat_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R u C J T D K : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val)
    (hu : M.mem (u.eval ρ).val (A.eval ρ).val) (hC : Scode_d I ω (C.eval ρ).val)
    (hJ : Fseq_space_d I ω (A.eval ρ).val (J.eval ρ).val)
    (hT : M.IsCartesianProduct I (T.eval ρ).val (C.eval ρ).val ω)
    (hD : M.IsCartesianProduct I (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo I (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_select_m w A R u C J T D K) ↔
      Ssk_d I ω c (A.eval ρ).val (u.eval ρ).val (C.eval ρ).val (J.eval ρ).val
        (T.eval ρ).val (D.eval ρ).val (K.eval ρ).val := by
  have pair {e} (η : Env (rt_model_l Z hz) e) (p a b : Term e) :
      Formula.satisfies η (kpair0_m p a b) ↔ KPair_d M (p.eval η).val (a.eval η).val (b.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (kpair0_delta_l p a b) η).trans (kpair0_sat_l hZF.1 ..)
  have entry {e} (η : Env (rt_model_l Z hz) e) (a b f : Term e) :
      Formula.satisfies η (rd_entry0_m a b f) ↔ Rd_entry_d (a.eval η).val (b.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (rd_entry0_delta_l a b f) η).trans (rd_entry0_sat_l hZF.1 ..)
  simp only [sh_select_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, pair, entry,
    sh_choice_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    fw_relative_sat_l (ZF.modelsKP hZF) source.transitive hz,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 source.transitive hz),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hw]
  have wit a i s x (hi : M.mem i ω) (hx : M.mem x (A.eval ρ).val) :=
    source.finite_witness_l hZF (A.eval ρ).property (R.eval ρ).property hm hJ hu hi hx (a := a) (s := s)
  constructor
  · intro h
    refine ⟨hu, hC, hJ, hT, hD, hK, fun p x hpx => ?_⟩
    obtain ⟨t, ht, s, hs, hp⟩ := (hD p).mp (hK.input_mem_of_pairMember hpx)
    obtain ⟨a, ha, i, hi, hti⟩ := (hT t).mp ht
    have hx := hK.output_mem_of_pairMember hpx
    let v : {x // M.mem x Z} := ⟨x, source.transitive _ (A.eval ρ).property x hx⟩
    have choice := h ⟨a, source.transitive _ (C.eval ρ).property a ha⟩ ha
      ⟨i, source.transitive ω source.omega_mem i hi⟩ (hw.symm ▸ hi)
      ⟨t, source.transitive _ (T.eval ρ).property t ht⟩ ht
      ⟨s, source.transitive _ (J.eval ρ).property s hs⟩ hs
      ⟨p, source.transitive _ (D.eval ρ).property p (hK.input_mem_of_pairMember hpx)⟩
      (hK.input_mem_of_pairMember hpx) v hx hti hp hpx
    refine ⟨a, i, t, s, hti, hp, ?_⟩
    rcases choice with h | ⟨none, eq⟩
    · exact Or.inl ((wit a i s x hi hx).mp h)
    · refine Or.inr ⟨?_, congrArg Subtype.val eq⟩
      rintro ⟨y, hy, ht⟩
      exact none ⟨y, source.transitive _ (A.eval ρ).property y hy⟩ hy ((wit a i s y hi hy).mpr ht)
  · intro h a _ i hi t _ s _ p _ x hx ht hp hpx
    have hi : M.mem i.val ω := hw ▸ hi
    rcases h.value_l I ht hp hpx with ht | ⟨none, eq⟩
    · exact Or.inl ((wit a.val i.val s.val x.val hi hx).mpr ht)
    · exact Or.inr ⟨fun y hy h => none ⟨y.val, hy, (wit a.val i.val s.val y.val hi hy).mp h⟩, Subtype.ext eq⟩

theorem Ep_source_d.skolem_sat_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R u C J T D K : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val) :
    Formula.satisfies ρ (sh_skolem_m w A R u C J T D K) ↔
      Ssk_d I ω c (A.eval ρ).val (u.eval ρ).val (C.eval ρ).val (J.eval ρ).val
        (T.eval ρ).val (D.eval ρ).val (K.eval ρ).val := by
  have prod (P A B : Term d) : Formula.satisfies ρ (sh_product_m P A B) ↔
      M.IsCartesianProduct I (P.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (sh_product_delta_l P A B) ρ).trans (sh_product_sat_l (ZF.modelsKP hZF) ..)
  have fn : Formula.satisfies ρ (fn0_m D A K) ↔ Fn0_d (D.eval ρ).val (A.eval ρ).val (K.eval ρ).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (fn0_delta_l D A K) ρ).trans (fn0_sat_l hZF.1 ..)
  simp only [sh_skolem_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, prod, fn, hw]
  rw [source.codes_sat_l hZF hz ρ w C hw, source.sequences_sat_l hZF hz ρ w A J hw]
  exact ⟨fun ⟨hu, hC, hJ, hT, hD, hK, hs⟩ => (source.select_sat_l hZF hz ρ w A R u C J T D K hw hm
    hu hC hJ hT hD (fn0_function_l (ZF.modelsKP hZF) hK)).mp hs,
    fun h => ⟨h.point, h.codes, h.params, h.labels, h.domain, fn0_of_function_l (ZF.modelsKP hZF) h.graph,
      (source.select_sat_l hZF hz ρ w A R u C J T D K hw hm h.point h.codes h.params h.labels h.domain h.graph).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 模型内小 Skolem 壳的全参数传输

传输的是完整的全称存在句子，因此后继中的新结构和新种子同样适用。
读取结果包含源内的实际选择图、相对最小闭包及序数上的双射图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.skolem_output_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R U μ : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val) :
    Formula.satisfies ρ (sh_output_m w A R U μ) ↔
      Sh_data_d (ZF.modelsKP hZF) Z ω c (A.eval ρ).val (U.eval ρ).val (μ.eval ρ).val := by
  let v (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have read (u C J T D K N f : (rt_model_l Z hz).Domain) :
      Formula.satisfies ((((((((ρ.push u).push C).push J).push T).push D).push K).push N).push f)
        (.conj (sh_skolem_m (v w) (v A) (v R) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
          (.conj (sh_hull_m (v w) (v A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (v U) (.bound 1))
            (sh_bijection_m .newest (v μ) (.bound 1)))) ↔
        Ssk_d I ω c (A.eval ρ).val u.val C.val J.val T.val D.val K.val ∧
          Sh_hull_d (ZF.modelsKP hZF) Z ω (A.eval ρ).val T.val K.val (U.eval ρ).val N.val ∧
            M.IsSetBijectionFromTo I f.val (μ.eval ρ).val N.val := by
    let η := ((((((((ρ.push u).push C).push J).push T).push D).push K).push N).push f)
    have sk := source.skolem_sat_l hZF hz η (v w) (v A) (v R)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      (by simpa only [η, v, Definitional.Term.eval_weaken] using hw)
      (by simpa only [η, v, Definitional.Term.eval_weaken] using hm)
    simp only [η, v, Definitional.Term.eval_weaken] at sk
    rw [Formula.satisfies_conj_iff, sk]
    apply and_congr_right
    intro h
    have hull := sh_hull_relative_l (ZF.modelsKP hZF) source.transitive hz η
      (v w) (v A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (v U) (.bound 1)
      (by simpa only [η, v, Definitional.Term.eval_weaken, hw] using h.params) h.domain
      (by simpa only [η, v, Definitional.Term.eval_weaken] using h.graph)
    have bij := (rt_model_delta_l source.transitive hz (sh_bijection_delta_l .newest (v μ) (.bound 1)) η).trans
      (sh_bijection_sat_l (ZF.modelsKP hZF) ..)
    have tr := and_congr hull bij
    simp only [η, v, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val,
      Definitional.Term.eval_weaken, hw] at tr
    change _ ↔ (Sh_hull_d (ZF.modelsKP hZF) Z ω (A.eval ρ).val T.val K.val (U.eval ρ).val N.val ∧
      M.IsSetBijectionFromTo I f.val (μ.eval ρ).val N.val) at tr
    exact (Formula.satisfies_conj_iff ..).trans tr
  simp only [sh_output_m, Formula.satisfies_exists_iff]
  constructor
  · rintro ⟨u, C, J, T, D, K, N, f, h⟩
    exact ⟨u.val, C.val, J.val, T.val, D.val, K.val, N.val, f.val,
      u.property, C.property, J.property, T.property, D.property, K.property, N.property, f.property,
      (read u C J T D K N f).mp h⟩
  · rintro ⟨u, C, J, T, D, K, N, f, hu, hC, hJ, hT, hD, hK, hN, hf, h⟩
    exact ⟨⟨u, hu⟩, ⟨C, hC⟩, ⟨J, hJ⟩, ⟨T, hT⟩, ⟨D, hD⟩, ⟨K, hK⟩, ⟨N, hN⟩, ⟨f, hf⟩,
      (read ⟨u, hu⟩ ⟨C, hC⟩ ⟨J, hJ⟩ ⟨T, hT⟩ ⟨D, hD⟩ ⟨K, hK⟩ ⟨N, hN⟩ ⟨f, hf⟩).mpr h⟩

theorem Ep_source_d.skolem_source_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) (ρ : Env (rt_model_l Z hz) 1) (hw : (ρ.bound 0).val = ω) :
    Formula.satisfies ρ (sh_source_m .newest) ↔ Sh_source_d (ZF.modelsKP hZF) ω Z := by
  have input (A R U μ f : (rt_model_l Z hz).Domain) :
      Formula.satisfies (((((ρ.push A).push R).push U).push μ).push f)
        (sh_input_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔
      M.IsOrdinal μ.val ∧ M.MemberSubset ω μ.val ∧ M.MemberSubset U.val A.val ∧
        M.IsSetBijectionFromTo I f.val μ.val U.val ∧ M.IsSetRelationOn I R.val A.val := by
    have tr := (rt_model_delta_l source.transitive hz
      (sh_input_delta_l (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (((((ρ.push A).push R).push U).push μ).push f)).trans (sh_input_sat_l (ZF.modelsKP hZF) ..)
    change _ ↔ (M.IsOrdinal μ.val ∧ M.MemberSubset (ρ.bound 0).val μ.val ∧ M.MemberSubset U.val A.val ∧
      M.IsSetBijectionFromTo I f.val μ.val U.val ∧ M.IsSetRelationOn I R.val A.val) at tr
    exact hw ▸ tr
  have output {c} (A R U μ f : (rt_model_l Z hz).Domain) (hm : Smdl_d I c A.val R.val) :=
    source.skolem_output_l hZF hz (((((ρ.push A).push R).push U).push μ).push f)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) hw hm
  simp only [sh_source_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff]
  constructor
  · intro h c A R U μ f hA hR hU hμ hf hm ho hωμ hUA bij
    exact (output ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩ hm).mp
      (h ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩
        ((input ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩).mpr ⟨ho, hωμ, hUA, bij, hm.2.2⟩))
  · intro h A R U μ f hi
    obtain ⟨ho, hωμ, hUA, bij, relation⟩ := (input A R U μ f).mp hi
    obtain ⟨z, _, hzω⟩ := source.omega.1.1
    obtain ⟨x, hx, _⟩ := bij.1.1.2.2 z (hωμ z hzω)
    obtain ⟨c, hc⟩ := (kp_pair_l (ZF.modelsKP hZF)).total A.val R.val
    have hm : Smdl_d I c A.val R.val := ⟨hc, ⟨x, hUA x hx⟩, relation⟩
    exact (output A R U μ f hm).mpr
      (h c A.val R.val U.val μ.val f.val A.property R.property U.property μ.property f.property hm ho hωμ hUA bij)

theorem sh_source_iff_l {ω κ K X R μ L Y S c d q : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ L Y S) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hq : Smap_d I ω c d X Y q) : Sh_source_d (ZF.modelsKP hZF) ω X ↔ Sh_source_d (ZF.modelsKP hZF) ω Y := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, source.omega_mem⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨ω, target.omega_mem⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hq⟩
    nx ny (sh_source_m .newest) (by simp -implicitDefEqProofs) ρ η
    (fun _ => hq.omega_l I hZF source.omega source.transitive target.transitive hm hn source.omega_mem)
  exact (source.skolem_source_sat_l hZF nx ρ rfl).symm.trans (tr.trans (target.skolem_source_sat_l hZF ny η rfl))

/-- 小壳理论和原源数据一同传给初等后继，并允许换用后继中的新大小参数。 -/
theorem Ep_source_d.skolem_successor_l {ω κ K X R c d N W j μ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (h : Sh_source_d (ZF.modelsKP hZF) ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d N W) (hN : M.TransitiveSet N)
    (hj : Smap_d I ω c d X N j) (hμ : M.mem μ N) (hωμ : M.MemberSubset ω μ) (small : Rf_small_d (kp_pair_l (ZF.modelsKP hZF)) N W μ) :
    ∃ L, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ L N W ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨L, target⟩ := source.successor_l hZF hm hn hN hj hμ hωμ small
  exact ⟨L, target, (sh_source_iff_l hZF source target hm hn hj).mp h⟩

end YesMetaZFC.SetTheory.LargeCardinal
