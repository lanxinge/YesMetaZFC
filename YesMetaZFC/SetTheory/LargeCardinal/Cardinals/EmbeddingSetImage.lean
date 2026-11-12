import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 全内部初等图在源内集合上的限制

有限真值表属于原源，沿嵌入搬运后仍解释同一个内部程序。限制因此保持
全部内部公式，包含非标准有限长度；没有以外部逐公式初等性替代原证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem er_program_l {ω κ K X R Y S c d j n F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hF : Sfm_d I ω n F) : Rd_entry_d F F j := by
  obtain ⟨hFX, b, L, hL, program⟩ := source.program_l hZF hF
  obtain ⟨F', _, hFF⟩ := hj.1.1.2.2 F hFX
  obtain ⟨L', _, hLL⟩ := hj.1.1.2.2 L hL
  have nat := hj.natural_l hZF source.omega source.transitive hY hm hn source.omega_mem
  have fn := (hj.function_l hZF source.omega source.transitive hY hm hn (nat n hF.1) hLL hFF).mp program.2.2.1
  have fixed k a i r (hs : Sop_d I k a i r) (hi : M.mem i ω) (hr : M.mem r ω)
      (ha : M.mem a X) : Rd_entry_d a a j := by
    obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a ha
    have tr := smap_delta_l I hZF source.omega source.transitive hY hm hn hj (n := 3)
      (sop0_m k (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (sop0_delta_l ..)
      ⟨Fin.cases r (Fin.cases i (fun _ => a)), fun _ => a⟩
      ⟨Fin.cases r (Fin.cases i (fun _ => a')), fun _ => a'⟩ (Fin.cases (nat r hr) (Fin.cases (nat i hi) (fun _ => haa)))
    obtain ⟨u, o, ho, hu, ha'⟩ := (sop0_sat_l (ZF.modelsKP hZF) ..).mp (tr.mp ((sop0_sat_l (ZF.modelsKP hZF) ..).mpr hs))
    obtain ⟨v, p, hp, hv, hap⟩ := hs
    have eq := num_unique_l hZF.1 ho hp
    subst p
    have eq := kpair_unique_l M hZF.1 hu hv
    subst v
    exact kpair_unique_l M hZF.1 ha' hap ▸ haa
  have eq := fn.ext_l hZF.1 program.2.2.1 (fun r hr => by
    obtain ⟨a, ha, hra⟩ := program.2.2.1.2.1 r hr
    have hrω := source.omega.transitive (ZF.modelsKP hZF) n hF.1 r hr
    have keep : Rd_entry_d a a j := by
      have haX := source.transitive L hL a ha
      rcases hF.2.2 r a hra with ⟨i, k, hs, hi, hk⟩ | ⟨i, k, hs, hi, hk⟩ |
        ⟨i, k, hs, hi, hk⟩ | ⟨i, k, hs, hi, hk⟩
      · exact fixed 0 a i k hs hi hk haX
      · exact fixed 1 a i k hs hi hk haX
      · exact fixed 2 a i k hs (source.omega.transitive (ZF.modelsKP hZF) r hrω i hi) (source.omega.transitive (ZF.modelsKP hZF) r hrω k hk) haX
      · exact fixed 3 a i k hs hi (source.omega.transitive (ZF.modelsKP hZF) r hrω k hk) haX
    exact ⟨a, (hj.entry_l hZF source.omega source.transitive hY hm hn (nat r hrω) keep hFF).mp hra, hra⟩)
  exact eq ▸ hFF

/-- 源内集合的实际隶属关系随集合一起搬运。 -/
theorem ep_set_membership_l {ω κ K X R μ K' Y S c d j a A Q b B T : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ha : Smem_d I a A Q) (hb : Smem_d I b B T) (hAB : Rd_entry_d A B j) : Rd_entry_d Q T j := by
  have read {a A Q} (model : Smem_d I a A Q) p : M.mem p Q ↔
      ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧ KPair_d M p x y ∧ M.mem x y := by
    refine ⟨fun hp => ?_, fun ⟨x, hx, y, hy, hp, hxy⟩ => ?_⟩
    · obtain ⟨x, y, hp'⟩ := model.1.2.2.1 p hp
      obtain ⟨hx, hy, hxy⟩ := (model.2 x y).mp ⟨p, hp', hp⟩
      exact ⟨x, hx, y, hy, hp', hxy⟩
    · obtain ⟨q, hq, hqQ⟩ := (model.2 x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 hq hp ▸ hqQ
  obtain ⟨Q', hQ', hQQ⟩ := hj.1.1.2.2 Q (source.membership_relation_l hZF (hj.1.1.input_mem_of_pairMember hAB) ha)
  have hT := target.membership_relation_l hZF (hj.1.1.output_mem_of_pairMember hAB) hb
  let φ : Formula 1 3 := .iff (.mem .newest (.bound 1)) (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) .newest))))
  have tr := hj.forall_delta_l hZF source.omega source.transitive target.transitive hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.iff (.mem _ _) (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.mem _ _)))))
    ⟨Fin.cases Q (fun _ => A), fun _ => A⟩ ⟨Fin.cases Q' (fun _ => B), fun _ => B⟩ (Fin.cases hQQ (fun _ => hAB))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, kpair0_sat_l hZF.1] at tr
  have image := tr.mp (fun p _ => read ha p)
  have eq := hZF.1.eq_of_same_members Q' T (fun p =>
    ⟨fun hp => (read hb p).mpr ((image p (target.transitive Q' hQ' p hp)).mp hp),
      fun hp => (image p (target.transitive T hT p hp)).mpr ((read hb p).mp hp)⟩)
  exact eq ▸ hQQ

/-- 搬运整张有限真值表，目标表同时解释不在 j 像中的赋值。 -/
theorem ep_set_tables_l {ω κ K X R μ K' Y S c d j A Q B T b n F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hAB : Rd_entry_d A B j) (hQT : Rd_entry_d Q T j)
    (hF : Sfm_d I ω n F) (hbo : M.mem b ω) (bound : Sbound_d I F b) :
    ∃ E D C H C' H', M.IsFunctionSpace I E b A ∧ M.IsFunctionSpace I D b B ∧
      Rd_entry_d E D j ∧ Rd_entry_d C C' j ∧ Rd_entry_d H H' j ∧
      (∀ r, M.mem r n → ∀ f, Fv_at_d C H r f ↔ Ssat_d I A Q E F n r f) ∧
      (∀ r, M.mem r n → ∀ f, Fv_at_d C' H' r f ↔ Ssat_d I B T D F n r f) := by
  have hA := hj.1.1.input_mem_of_pairMember hAB
  have hQ := hj.1.1.input_mem_of_pairMember hQT
  obtain ⟨E, hE, space⟩ := source.finite_space_l hZF hA hbo
  obtain ⟨D, _, hED⟩ := hj.1.1.2.2 E hE
  have space' : M.IsFunctionSpace I D b B := fun g =>
    (ep_space_map_l hZF source target hm hn hj hAB hbo
      (fun f => (space f).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩) hED g).trans
      ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩
  obtain ⟨_, _, L, hL, old⟩ := source.program_l hZF hF
  have program := fb_program_of_l (ZF.modelsKP hZF) hF hbo bound old.2.2.1
  obtain ⟨C, H, hC, hH, table⟩ := source.finite_evaluation_l hZF hA hQ hE program space
  obtain ⟨L', _, hLL⟩ := hj.1.1.2.2 L hL
  obtain ⟨C', _, hCC⟩ := hj.1.1.2.2 C hC
  obtain ⟨H', _, hHH⟩ := hj.1.1.2.2 H hH
  have nat := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have hFF := er_program_l hZF source target.transitive hm hn hj hF
  have pr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj (n := 5)
    (fb_program_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fb_program_delta_l ..)
    ⟨Fin.cases F (Fin.cases L (Fin.cases n (Fin.cases b (fun _ => ω)))), fun _ => ω⟩
    ⟨Fin.cases F (Fin.cases L' (Fin.cases n (Fin.cases b (fun _ => ω)))), fun _ => ω⟩
    (Fin.cases hFF (Fin.cases hLL (Fin.cases (nat n hF.1) (Fin.cases (nat b hbo)
      (fun _ => hj.omega_l I hZF source.omega source.transitive target.transitive hm hn source.omega_mem)))))
  have program' := (fb_program_sat_l (ZF.modelsKP hZF) ..).mp (pr.mp ((fb_program_sat_l (ZF.modelsKP hZF) ..).mpr program))
  have ev := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj (n := 9)
    (fv_eval_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fv_eval_delta_l ..)
    ⟨Fin.cases H (Fin.cases C (Fin.cases F (Fin.cases L (Fin.cases n (Fin.cases E (Fin.cases Q (Fin.cases A (fun _ => b)))))))), fun _ => b⟩
    ⟨Fin.cases H' (Fin.cases C' (Fin.cases F (Fin.cases L' (Fin.cases n (Fin.cases D (Fin.cases T (Fin.cases B (fun _ => b)))))))), fun _ => b⟩
    (Fin.cases hHH (Fin.cases hCC (Fin.cases hFF (Fin.cases hLL (Fin.cases (nat n hF.1)
      (Fin.cases hED (Fin.cases hQT (Fin.cases hAB (fun _ => nat b hbo)))))))))
  have table' := (fv_eval_sat_l (ZF.modelsKP hZF) ..).mp (ev.mp ((fv_eval_sat_l (ZF.modelsKP hZF) ..).mpr table))
  exact ⟨E, D, C, H, C', H', space, space', hED, hCC, hHH,
    fun r hr f => table.truth_l hZF source.omega program space hr (f := f),
    fun r hr f => table'.truth_l hZF target.omega program' space' hr (f := f)⟩

private theorem er_truth_l {ω κ K X R μ K' Y S c d j A Q B T b n F r f g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hAB : Rd_entry_d A B j) (hQT : Rd_entry_d Q T j)
    (hF : Sfm_d I ω n F) (hbo : M.mem b ω) (bound : Sbound_d I F b) (hr : M.mem r n)
    (hfg : Rd_entry_d f g j) : ∃ E D, M.IsFunctionSpace I E b A ∧ M.IsFunctionSpace I D b B ∧
      (Ssat_d I A Q E F n r f ↔ Ssat_d I B T D F n r g) := by
  obtain ⟨E, D, C, H, C', H', space, space', _, hCC, hHH, left, right⟩ :=
    ep_set_tables_l hZF source target hm hn hj hAB hQT hF hbo bound
  have nat := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have value := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj (n := 4)
    (fv_at_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fv_at_delta_l ..)
    ⟨Fin.cases f (Fin.cases r (Fin.cases H (fun _ => C))), fun _ => C⟩
    ⟨Fin.cases g (Fin.cases r (Fin.cases H' (fun _ => C'))), fun _ => C'⟩
    (Fin.cases hfg (Fin.cases (nat r (source.omega.transitive (ZF.modelsKP hZF) n hF.1 r hr)) (Fin.cases hHH (fun _ => hCC))))
  simp only [fv_at_sat_l hZF.1] at value
  exact ⟨E, D, space, space', (left r hr f).symm.trans (value.trans (right r hr g))⟩

/-- 载体与原关系共同搬运时，实际限制 j↾A 保持全部内部程序的真值。 -/
theorem ep_set_restriction_l {ω κ K X R μ K' Y S c d j a A Q b B T : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ha : Smdl_d I a A Q) (hb : Smdl_d I b B T)
    (hAB : Rd_entry_d A B j) (hQT : Rd_entry_d Q T j) :
    ∃ p, M.IsRestrictionOf I p j A ∧ Smap_d I ω a b A B p := by
  have hA := hj.1.1.input_mem_of_pairMember hAB
  obtain ⟨p, res⟩ := ZF.exists_restriction hZF I j A
  have fn := fn0_of_function_l (ZF.modelsKP hZF) (res.isSetFunctionFromTo hj.1.1 (source.transitive A hA))
  have into x y (hxy : Rd_entry_d x y p) : M.mem y B :=
    ((hn.2 y B).mp ((hj.relation_l I hZF source.omega hm.1 hn.1 ((res.2 x y).mp hxy).2 hAB).mp
      ((hm.2 x A).mpr ⟨source.transitive A hA x (fn.bound_l hxy).1, hA, (fn.bound_l hxy).1⟩))).2.2
  obtain ⟨C, codes⟩ := scode_exists_l I hZF source.omega
  refine ⟨p, res, ⟨fn0_function_l (ZF.modelsKP hZF) (fn.retarget_l into),
    fun x y z hx hy => hj.1.2 x y z ((res.2 x z).mp hx).2 ((res.2 y z).mp hy).2⟩, C, codes, ?_⟩
  intro v f g hv hf hg assign
  obtain ⟨n, F, r, code⟩ := (codes v).mp hv
  obtain ⟨l, hl, bound⟩ := sbound_exists_l I hZF source.omega code.2.1
  have sub := source.omega.transitive (ZF.modelsKP hZF) l hl
  obtain ⟨s, fs⟩ := ZF.exists_restriction hZF I f l
  obtain ⟨t, gt⟩ := ZF.exists_restriction hZF I g l
  have sf := fn0_of_function_l (ZF.modelsKP hZF) (fs.isSetFunctionFromTo hf sub)
  have tf := fn0_of_function_l (ZF.modelsKP hZF) (gt.isSetFunctionFromTo hg sub)
  have hs := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
    (source.transitive A hA) hl sf
  obtain ⟨t', _, hst⟩ := hj.1.1.2.2 s hs
  have nat := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have image := (hj.function_l hZF source.omega source.transitive target.transitive hm hn (nat l hl) hAB hst).mp sf
  have eq := image.ext_l hZF.1 tf (fun i hi => by
    obtain ⟨x, hx, hix⟩ := sf.2.1 i hi
    obtain ⟨y, _, hxy⟩ := (fn.retarget_l into).2.1 x hx
    exact ⟨y, (hj.entry_l hZF source.omega source.transitive target.transitive hm hn (nat i (sub i hi))
      ((res.2 x y).mp hxy).2 hst).mp hix,
      (gt.2 i y).mpr ⟨hi, assign i (sub i hi) x y ((fs.2 i x).mp hix).2 hxy⟩⟩)
  have hst := eq ▸ hst
  obtain ⟨E, D, hE, hD, truth⟩ := er_truth_l hZF source target hm hn hj hAB hQT code.2.1 hl bound code.2.2 hst
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
  have left := ssat_spaces_l I hZF (R := Q) code.2.1 bound hE₀ hE sub (fun _ h => h) code.2.2
    ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) sf))
    (fun i x hi => ((fs.2 i x).trans (and_iff_right hi)).symm)
  have right := ssat_spaces_l I hZF (R := T) code.2.1 bound hD₀ hD sub (fun _ h => h) code.2.2
    ((hD₀ g).mpr hg) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) tf))
    (fun i x hi => ((gt.2 i x).trans (and_iff_right hi)).symm)
  exact (satisfies_decode_l I hZF.1 ha code hE₀).trans
    (left.trans (truth.trans (right.symm.trans (satisfies_decode_l I hZF.1 hb code hD₀).symm)))

/-- 拥有的函数图可沿外层初等嵌入反射完整初等性；证明使用两端集合上的实际限制。 -/
theorem ep_set_map_pull_l {ω κ K V R μ K' W S c d j a A P a' A' P' b B Q b' B' Q' f g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K V R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' W S)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W j)
    (ma : Smdl_d I a A P) (ma' : Smdl_d I a' A' P')
    (mb : Smdl_d I b B Q) (mb' : Smdl_d I b' B' Q')
    (hA : Rd_entry_d A A' j) (hP : Rd_entry_d P P' j)
    (hB : Rd_entry_d B B' j) (hQ : Rd_entry_d Q Q' j) (hf : Rd_entry_d f g j)
    (hg : Smap_d I ω a' b' A' B' g) : Smap_d I ω a b A B f := by
  obtain ⟨p, rp, hp⟩ := ep_set_restriction_l hZF source target mv mw hj ma ma' hA hP
  obtain ⟨q, rq, hq⟩ := ep_set_restriction_l hZF source target mv mw hj mb mb' hB hQ
  have fn := (hj.function_l hZF source.omega source.transitive target.transitive mv mw hA hB hf).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) hg.1.1)
  obtain ⟨s, hs, comp⟩ := smap_comp_l I hZF hp hg
  apply smap_factor_l I hZF hs hq (fn0_function_l (ZF.modelsKP hZF) fn)
  intro x y z hxy hyz
  obtain ⟨x', _, hxx⟩ := hp.1.1.2.2 x (fn.bound_l hxy).1
  exact (comp x z).mpr ⟨(fn.bound_l hxy).1, x', hxx,
    (hj.entry_l hZF source.omega source.transitive target.transitive mv mw
      ((rp.2 x x').mp hxx).2 ((rq.2 y z).mp hyz).2 hf).mp hxy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系结构及其完整像的实际坐标双射

结构码、载体和关系一起搬运。原载体的完整像条件使嵌入限制成为真实
双射；其逆图保留全部内部公式，供复制时在移动的坐标之间换算。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_model_image_l {ω c Z R d U S j a A P b B Q : M.Domain}
    (hω : M.IsOmega ω) (zt : M.TransitiveSet Z) (ut : M.TransitiveSet U)
    (mz : Smem_d I c Z R) (mu : Smem_d I d U S) (hj : Smap_d I ω c d Z U j)
    (ma : Smdl_d I a A P) (hab : Rd_entry_d a b j)
    (hAB : Rd_entry_d A B j) (hPQ : Rd_entry_d P Q j) : Smdl_d I b B Q := by
  have pair := (hj.kpair_l hZF hω zt ut mz mu hab hAB hPQ).mp ma.1
  obtain ⟨x, hx⟩ := ma.2.1
  obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x (zt A (hj.1.1.input_mem_of_pairMember hAB) x hx)
  have hy := (hj.member_l I hZF hω mz mu hxy hAB).mp hx
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := smap_delta_l I hZF hω zt ut mz mu hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases P (fun _ => A), fun _ => A⟩ ⟨Fin.cases Q (fun _ => B), fun _ => B⟩ (Fin.cases hPQ (fun _ => hAB))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mp (fun p hp => by
    obtain ⟨x, y, pair⟩ := ma.2.2.1 p hp
    have bounds := ma.2.2.2 x y ⟨p, pair, hp⟩
    exact ⟨x, bounds.1, y, bounds.2, pair⟩)
  refine ⟨pair, ⟨y, hy⟩, ⟨?_, ?_⟩⟩
  · intro p hp
    obtain ⟨x, _, y, _, pair⟩ := shape p hp
    exact ⟨x, y, pair⟩
  · intro x y hxy
    obtain ⟨p, pair, hp⟩ := hxy
    obtain ⟨x', hx, y', hy, pair'⟩ := shape p hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ⟨hx, hy⟩

/-- 同一拥有结构的完整像给出两个方向的实际全初等坐标图。 -/
theorem ep_set_iso_image_l {ω c Z R d U S j a A P b B Q : M.Domain}
    (hω : M.IsOmega ω) (zt : M.TransitiveSet Z) (ut : M.TransitiveSet U)
    (mz : Smem_d I c Z R) (mu : Smem_d I d U S) (hj : Smap_d I ω c d Z U j)
    (ma : Smdl_d I a A P) (hab : Rd_entry_d a b j)
    (hAB : Rd_entry_d A B j) (hPQ : Rd_entry_d P Q j)
    (onto : ∀ y, M.mem y B → ∃ x, M.mem x A ∧ Rd_entry_d x y j) :
    ∃ f g, Smdl_d I b B Q ∧ M.IsSetBijectionFromTo I f A B ∧
      Smap_d I ω a b A B f ∧ Smap_d I ω b a B A g ∧
      (∀ x y, Rd_entry_d x y f ↔ M.mem x A ∧ Rd_entry_d x y j) ∧
      ∀ y x, Rd_entry_d y x g ↔ Rd_entry_d x y f := by
  have mb := ep_set_model_image_l hZF hω zt ut mz mu hj ma hab hAB hPQ
  obtain ⟨f, res⟩ := ZF.exists_restriction hZF I j A
  have base := res.isSetFunctionFromTo hj.1.1 (zt A (hj.1.1.input_mem_of_pairMember hAB))
  have fn : M.IsSetFunctionFromTo I f A B := ⟨base.1, base.2.1, fun x hx => by
    obtain ⟨y, _, hxy⟩ := base.2.2 x hx
    exact ⟨y, (hj.member_l I hZF hω mz mu ((res.2 x y).mp hxy).2 hAB).mp hx, hxy⟩⟩
  have bij : M.IsSetBijectionFromTo I f A B := ⟨⟨fn, fun x y v hx hy =>
    hj.1.2 x y v ((res.2 x v).mp hx).2 ((res.2 y v).mp hy).2⟩,
    fun y hy => (onto y hy).imp fun x hx => ⟨hx.1, (res.2 x y).mpr hx⟩⟩
  have atom x y v w (hx : Rd_entry_d x v f) (hy : Rd_entry_d y w f) : Rd_entry_d x y P ↔ Rd_entry_d v w Q :=
    hj.entry_l hZF hω zt ut mz mu ((res.2 x v).mp hx).2 ((res.2 y w).mp hy).2 hPQ
  have forward := smap_of_iso_l I hZF hω ma mb bij atom
  obtain ⟨g, back, gs⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have inverse := smap_of_iso_l I hZF hω mb ma back (fun v w x y hx hy =>
    (atom x y v w ((gs v x).mp hx) ((gs w y).mp hy)).symm)
  exact ⟨f, g, mb, bij, forward, inverse, res.2, gs⟩

end YesMetaZFC.SetTheory.LargeCardinal
