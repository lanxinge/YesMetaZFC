import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchive
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundParity

/-! # 一般原模型中的实际请求

请求记录、选定共同图列、原生端点界和根切片共同保存。所有低层所属
均在原关系中解释；没有工作复制行，也没有背景 Vγ 或外部良基性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Tg_raw_request_d (Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ X R w η C χ z k D r q : M.Domain)
    (f : Tg_raw_archive_frame_d M.Domain) (v : Fin 46 → M.Domain) : Prop where
  context : Tg_context_d I w X R η C
  record : Rf_record_d I X R tg_issued0_m C r
  values : Rf_tuple_d I X R v r
  omega : v 0 = w
  external_omega : M.IsOmega Ω
  numbers : Rr_layer_d I Ω X R w z
  finite : M.mem k Ω
  index : M.PairMember I k (v 19) z
  sequence : M.IsSequenceOfLength I D k
  links : Tg_raw_archive_links_d I f D
  origin : It_map_d f.G f.o f.n q
  name : Rd_entry_d S₀ (v 7) q
  alphabet : Rd_entry_d A₀ (v 6) q
  views : Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ q D X R χ w C (v 4) (v 1) (v 2) (v 3) z (v 20)
  ordinal : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => χ)
  below : Rd_entry_d χ (v 24) R
  slice : ∃ γ V t, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C q γ V t ∧
    Rd_entry_d w V R ∧ ∀ x, Rd_entry_d x γ R → Rd_entry_d x (v 24) R

/-- 原请求码直接恢复同一 issued 与外部轮号，根切片不参与原记录解码。 -/
theorem Tg_raw_request_d.read_l (hKP : M.Models KP)
    {Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ X R w η C χ z k D r q : M.Domain}
    {f : Tg_raw_archive_frame_d M.Domain} {v : Fin 46 → M.Domain}
    (h : Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ X R w η C χ z k D r q f v)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨w,h.context.omega_mem⟩)) :
    let N := smdl_structure_l I (R := R) ⟨w,h.context.omega_mem⟩
    let Cn : N.Domain := ⟨C,h.context.member⟩
    ∃ nc : Nonempty {x : N.Domain // N.mem x Cn}, ∃ ι : Env (rt_model_l Cn nc) 46,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
      Tg_round_index_d I Ω z ⟨w,h.context.omega_mem⟩ ⟨w,h.context.omega_mem⟩ (ι.bound 19).val k := by
  intro N Cn
  have fs := h.context.finite_l ⟨w,h.context.omega_mem⟩ ext
  let nc : Nonempty {x : N.Domain // N.mem x Cn} := ⟨⟨⟨w,h.context.omega_mem⟩,fs.omega_mem⟩⟩
  obtain ⟨ι,eq,issued⟩ := h.record.values_l I ⟨w,h.context.omega_mem⟩ ext tg_issued0_m tg_issued0_closed_l
    Cn ⟨r,h.record.elim fun mem _ => mem 1⟩ fs.transitive nc h.values
  have point : M.PairMember I k (ι.bound 19).val.val z := (eq 19).symm ▸ h.index
  obtain ⟨l,index⟩ := tg_round_index_l I hKP h.external_omega ⟨w,h.context.omega_mem⟩ ext
    ⟨w,h.context.omega_mem⟩ (ι.bound 19).val h.numbers ((h.numbers.image _).mpr ⟨k,h.finite,point⟩)
  have equal := h.numbers.injection.2 l k (ι.bound 19).val.val index.point point
  exact ⟨nc,ι,eq,issued,equal ▸ index⟩

end YesMetaZFC.SetTheory.LargeCardinal
