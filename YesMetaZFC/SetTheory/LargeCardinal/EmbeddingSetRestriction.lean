import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTransport

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
    (source : Ep_source_d hZF ω κ K X R) (hY : M.TransitiveSet Y)
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
    have hrω := source.omega.transitive hZF n hF.1 r hr
    have keep : Rd_entry_d a a j := by
      have haX := source.transitive L hL a ha
      rcases hF.2.2 r a hra with ⟨i, k, hs, hi, hk⟩ | ⟨i, k, hs, hi, hk⟩ |
        ⟨i, k, hs, hi, hk⟩ | ⟨i, k, hs, hi, hk⟩
      · exact fixed 0 a i k hs hi hk haX
      · exact fixed 1 a i k hs hi hk haX
      · exact fixed 2 a i k hs (source.omega.transitive hZF r hrω i hi) (source.omega.transitive hZF r hrω k hk) haX
      · exact fixed 3 a i k hs hi (source.omega.transitive hZF r hrω k hk) haX
    exact ⟨a, (hj.entry_l hZF source.omega source.transitive hY hm hn (nat r hrω) keep hFF).mp hra, hra⟩)
  exact eq ▸ hFF

private theorem er_membership_l {ω κ K X R μ K' Y S c d j a A Q b B T : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
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
theorem ep_set_tables_l {ω κ K X R μ K' Y S c d j a A Q a' B T b n F : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ha : Smem_d I a A Q) (hb : Smem_d I a' B T) (hAB : Rd_entry_d A B j)
    (hF : Sfm_d I ω n F) (hbo : M.mem b ω) (bound : Sbound_d I F b) :
    ∃ E D C H C' H', M.IsFunctionSpace I E b A ∧ M.IsFunctionSpace I D b B ∧
      Rd_entry_d E D j ∧ Rd_entry_d C C' j ∧ Rd_entry_d H H' j ∧
      (∀ r, M.mem r n → ∀ f, Fv_at_d C H r f ↔ Ssat_d I A Q E F n r f) ∧
      (∀ r, M.mem r n → ∀ f, Fv_at_d C' H' r f ↔ Ssat_d I B T D F n r f) := by
  have hA := hj.1.1.input_mem_of_pairMember hAB
  have hQ := source.membership_relation_l hZF hA ha
  have hQT := er_membership_l hZF source target hm hn hj ha hb hAB
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

private theorem er_truth_l {ω κ K X R μ K' Y S c d j a A Q a' B T b n F r f g : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ha : Smem_d I a A Q) (hb : Smem_d I a' B T) (hAB : Rd_entry_d A B j)
    (hF : Sfm_d I ω n F) (hbo : M.mem b ω) (bound : Sbound_d I F b) (hr : M.mem r n)
    (hfg : Rd_entry_d f g j) : ∃ E D, M.IsFunctionSpace I E b A ∧ M.IsFunctionSpace I D b B ∧
      (Ssat_d I A Q E F n r f ↔ Ssat_d I B T D F n r g) := by
  obtain ⟨E, D, C, H, C', H', space, space', _, hCC, hHH, left, right⟩ :=
    ep_set_tables_l hZF source target hm hn hj ha hb hAB hF hbo bound
  have nat := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have value := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj (n := 4)
    (fv_at_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fv_at_delta_l ..)
    ⟨Fin.cases f (Fin.cases r (Fin.cases H (fun _ => C))), fun _ => C⟩
    ⟨Fin.cases g (Fin.cases r (Fin.cases H' (fun _ => C'))), fun _ => C'⟩
    (Fin.cases hfg (Fin.cases (nat r (source.omega.transitive hZF n hF.1 r hr)) (Fin.cases hHH (fun _ => hCC))))
  simp only [fv_at_sat_l hZF.1] at value
  exact ⟨E, D, space, space', (left r hr f).symm.trans (value.trans (right r hr g))⟩

/-- 任意源内非空集合 A 的实际限制 j↾A，在 A 与 j(A) 之间保持完整内部初等性。 -/
theorem ep_set_restriction_l {ω κ K X R μ K' Y S c d j a A Q b B T : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ha : Smem_d I a A Q) (hb : Smem_d I b B T) (hAB : Rd_entry_d A B j) :
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
  have sub := source.omega.transitive hZF l hl
  obtain ⟨s, fs⟩ := ZF.exists_restriction hZF I f l
  obtain ⟨t, gt⟩ := ZF.exists_restriction hZF I g l
  have sf := fn0_of_function_l (ZF.modelsKP hZF) (fs.isSetFunctionFromTo hf sub)
  have tf := fn0_of_function_l (ZF.modelsKP hZF) (gt.isSetFunctionFromTo hg sub)
  have hs := sc_finite_function_l hZF source.omega source.transitive hm source.theory source.omega_mem
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
  obtain ⟨E, D, hE, hD, truth⟩ := er_truth_l hZF source target hm hn hj ha hb hAB code.2.1 hl bound code.2.2 hst
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
  have left := ssat_spaces_l I hZF (R := Q) code.2.1 bound hE₀ hE sub (fun _ h => h) code.2.2
    ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) sf))
    (fun i x hi => ((fs.2 i x).trans (and_iff_right hi)).symm)
  have right := ssat_spaces_l I hZF (R := T) code.2.1 bound hD₀ hD sub (fun _ h => h) code.2.2
    ((hD₀ g).mpr hg) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) tf))
    (fun i x hi => ((gt.2 i x).trans (and_iff_right hi)).symm)
  exact (satisfies_decode_l I hZF.1 ha.1 code hE₀).trans
    (left.trans (truth.trans (right.symm.trans (satisfies_decode_l I hZF.1 hb.1 code hD₀).symm)))

end YesMetaZFC.SetTheory.LargeCardinal
