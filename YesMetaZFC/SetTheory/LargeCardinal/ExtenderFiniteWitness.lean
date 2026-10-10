import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteEvaluation
import YesMetaZFC.Model.SetTheory.Internal.FiniteWitness

/-! # Skolem 见证的源内有限证书

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
    (source : Ep_source_d hZF ω κ K Z W) (hA : M.mem A Z) (hR : M.mem R Z)
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
    have sub := source.omega.transitive hZF b program.1
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
        (source.omega.transitive hZF l program.2.1 r code.2.2),
      hn, fn0_of_function_l (ZF.modelsKP hZF) hs, code.1, code.2.2, program,
      (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mpr hE, ev,
      (fw_env_read_l (ZF.modelsKP hZF) sub fill update gf (fn0_of_function_l (ZF.modelsKP hZF) tf)).mpr agree,
      (ev.truth_l hZF source.omega program hE code.2.2).mpr (same.mp truth)⟩

end YesMetaZFC.SetTheory.LargeCardinal
