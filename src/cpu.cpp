/*
 * Central Processing Unit (CPU)
 *
 * Copyright (C) 2009-2011 Udo Steinberg <udo@hypervisor.org>
 * Economic rights: Technische Universitaet Dresden (Germany)
 *
 * Copyright (C) 2012-2013 Udo Steinberg, Intel Corporation.
 * Copyright (C) 2014 Udo Steinberg, FireEye, Inc.
 * Copyright (C) 2015 Alexander Boettcher, Genode Labs GmbH
 *
 * This file is part of the NOVA microhypervisor.
 *
 * NOVA is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * NOVA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License version 2 for more details.
 */

#include "bits.hpp"
#include "cmdline.hpp"
#include "counter.hpp"
#include "gdt.hpp"
#include "hip.hpp"
#include "idt.hpp"
#include "lapic.hpp"
#include "mca.hpp"
#include "msr.hpp"
#include "pd.hpp"
#include "stdio.hpp"
#include "svm.hpp"
#include "tss.hpp"
#include "vmx.hpp"

char const * const Cpu::vendor_string[] =
{
    "Unknown",
    "GenuineIntel",
    "AuthenticAMD"
};

mword       Cpu::boot_lock;

// Order of these matters
unsigned    Cpu::online;
uint8       Cpu::acpi_id[NUM_CPU];
uint8       Cpu::apic_id[NUM_CPU];

unsigned    Cpu::id;
unsigned    Cpu::hazard;
uint8       Cpu::package[NUM_CPU];
uint8       Cpu::core[NUM_CPU];
uint8       Cpu::thread[NUM_CPU];

Cpu::Vendor Cpu::vendor;
uint8       Cpu::platform[NUM_CPU];
uint8       Cpu::family[NUM_CPU];
uint8       Cpu::model[NUM_CPU];
uint8       Cpu::stepping[NUM_CPU];
unsigned    Cpu::brand;
unsigned    Cpu::patch[NUM_CPU];
unsigned    Cpu::row;

uint32      Cpu::name[12];
uint32      Cpu::features[6];
bool        Cpu::bsp;
bool        Cpu::preemption;

bool invariant_tsc()
{
    uint32 eax, ebx, ecx, edx;
    Cpu::cpuid (0x80000007, eax, ebx, ecx, edx);
    return edx & 0x100;
}

struct Cpu_msr
{
    enum Register
    {
        IA32_POWER_CTL          = 0x1fc,
        IA32_ENERGY_PERF_BIAS   = 0x1b0,
        MSR_PM_ENABLE           = 0x770,
        MSR_HWP_INTERRUPT       = 0x773,
        MSR_HWP_REQUEST         = 0x774,
    };

    template <typename T>
    ALWAYS_INLINE
    static inline T read (Register msr)
    {
        mword h, l;
        asm volatile ("rdmsr" : "=a" (l), "=d" (h) : "c" (msr));
        return static_cast<T>(static_cast<uint64>(h) << 32 | l);
    }

    template <typename T>
    ALWAYS_INLINE
    static inline void write (Register msr, T val)
    {
        asm volatile (
            "wrmsr" : :
            "a" (static_cast<mword>(val)),
            "d" (static_cast<mword>(static_cast<uint64>(val) >> 32)),
            "c" (msr));
    }

    static void hwp_notification_irqs(bool on)
    {
        write<uint64>(MSR_HWP_INTERRUPT, on ? 1 : 0);
    }

    static void hardware_pstates(bool on)
    {
        write<uint64>(MSR_PM_ENABLE, on ? 1 : 0);
    }

    static void energy_efficiency_optimization(bool on)
    {
        enum { DEEO_SHIFT = 20 };
        enum { DEEO_MASK = 0x1 };
        uint64 val = read<uint64>(IA32_POWER_CTL);
        val &= ~(static_cast<uint64>(DEEO_MASK) << DEEO_SHIFT);
        val |= (static_cast<uint64>(on ? 1 : 0) & DEEO_MASK) << DEEO_SHIFT;
        write<uint64>(IA32_POWER_CTL, val);
    }

    enum class Hwp_epp
    {
        PERFORMANCE  = 0,
        BALANCED     = 127,
        POWER_SAVING = 255,
    };

    static void hwp_energy_perf_pref(Hwp_epp epp)
    {
        enum { EPP_SHIFT = 24 };
        enum { EPP_MASK = 0xff };
        uint64 val = read<uint64>(MSR_HWP_REQUEST);
        val &= ~(static_cast<uint64>(EPP_MASK) << EPP_SHIFT);
        val |= (static_cast<uint64>(epp) & EPP_MASK) << EPP_SHIFT;
        write<uint64>(MSR_HWP_REQUEST, val);
    }

    enum class Hwp_epb
    {
        PERFORMANCE  = 0,
        BALANCED     = 7,
        POWER_SAVING = 15,
    };

    static void hwp_energy_perf_bias(Hwp_epb epb)
    {
        enum { EPB_SHIFT = 0 };
        enum { EPB_MASK = 0xf };
        uint64 val = read<uint64>(IA32_ENERGY_PERF_BIAS);
        val &= ~(static_cast<uint64>(EPB_MASK) << EPB_SHIFT);
        val |= (static_cast<uint64>(epb) & EPB_MASK) << EPB_SHIFT;
        write<uint64>(IA32_ENERGY_PERF_BIAS, val);
    }
};

static int strcmp(const char *s1, const char *s2, size_t len = ~0UL)
{
    for (; *s1 && *s1 == *s2 && len; s1++, s2++, len--) ;
    return len ? *s1 - *s2 : 0;
}

struct Cpuid
{
    enum { MAX_LEAF_IDX = 7 };

    uint32 eax[MAX_LEAF_IDX];
    uint32 ebx[MAX_LEAF_IDX];
    uint32 ecx[MAX_LEAF_IDX];
    uint32 edx[MAX_LEAF_IDX];

    void init_leaf(unsigned idx) {
        Cpu::cpuid (idx, eax[idx], ebx[idx], ecx[idx], edx[idx]);
    }

    Cpuid() {
        Cpu::cpuid (0, eax[0], ebx[0], ecx[0], edx[0]);
        for (unsigned idx = 1; idx <= eax[0] && idx <= MAX_LEAF_IDX; idx++) {
            init_leaf(idx);
        }
    }

    enum class Vendor {
        INTEL,
        UNKNOWN,
    };

    enum { VENDOR_STRING_LENGTH = 12 };

    Vendor vendor() const
    {
        char str[VENDOR_STRING_LENGTH];
        unsigned idx { 0 };
        for (unsigned shift = 0; shift <= 24; shift += 8, idx++) {
           str[idx] = static_cast<char>(ebx[0] >> shift);
        }
        for (unsigned shift = 0; shift <= 24; shift += 8, idx++) {
           str[idx] = static_cast<char>(edx[0] >> shift);
        }
        for (unsigned shift = 0; shift <= 24; shift += 8, idx++) {
           str[idx] = static_cast<char>(ecx[0] >> shift);
        }
        if (!strcmp(str, "GenuineIntel", VENDOR_STRING_LENGTH)) {
            return Vendor::INTEL;
        } else {
            return Vendor::UNKNOWN;
        }
    }

    using Family_id = uint32;
    enum { FAMILY_ID_UNKNOWN = ~static_cast<uint32>(0) };

    Family_id family_id() const
    {
        if (eax[0] < 1) {
            return FAMILY_ID_UNKNOWN;
        }
        enum { FAMILY_ID_SHIFT = 8 };
        enum { FAMILY_ID_MASK = 0xf };
        enum { EXT_FAMILY_ID_SHIFT = 20 };
        enum { EXT_FAMILY_ID_MASK = 0xff };
        Family_id family_id {
            (eax[1] >> FAMILY_ID_SHIFT) & FAMILY_ID_MASK };

        if (family_id == 15) {
            family_id += (eax[1] >> EXT_FAMILY_ID_SHIFT) & EXT_FAMILY_ID_MASK;
        }
        return family_id;
    }

    enum class Model {
        KABY_LAKE_DESKTOP,
        UNKNOWN,
    };

    Model model() const
    {
        if (eax[0] < 1) {
            return Model::UNKNOWN;
        }
        enum { MODEL_ID_SHIFT = 4 };
        enum { MODEL_ID_MASK = 0xf };
        enum { EXT_MODEL_ID_SHIFT = 16 };
        enum { EXT_MODEL_ID_MASK = 0xf };
        uint32 const fam_id { family_id() };
        uint32 model_id { (eax[1] >> MODEL_ID_SHIFT) & MODEL_ID_MASK };
        if (fam_id == 6 ||
            fam_id == 15)
        {
            model_id +=
                ((eax[1] >> EXT_MODEL_ID_SHIFT) & EXT_MODEL_ID_MASK) << 4;
        }
        switch (model_id) {
        case 0x9e: return Model::KABY_LAKE_DESKTOP;
        default:   return Model::UNKNOWN;
        }
    }

    bool hwp() const
    {
        if (eax[0] < 6) {
            return false;
        }
        return ((eax[6] >> 7) & 1) == 1;
    }

    bool hwp_notification() const
    {
        if (eax[0] < 6) {
            return false;
        }
        return ((eax[6] >> 8) & 1) == 1;
    }

    bool hwp_energy_perf_pref() const
    {
        if (eax[0] < 6) {
            return false;
        }
        return ((eax[6] >> 10) & 1) == 1;
    }

    bool hardware_coordination_feedback_cap() const
    {
        if (eax[0] < 6) {
            return false;
        }
        return ((ecx[6] >> 0) & 1) == 1;
    }

    bool hwp_energy_perf_bias() const
    {
        if (eax[0] < 6) {
            return false;
        }
        return ((ecx[6] >> 3) & 1) == 1;
    }
};

static void configure_hardware_pstates()
{
    char const* eeo_str { "" };
    char const* hwp_str { "" };
    char const* hwp_irq_str { "" };
    char const* hwp_epp_str { "" };
    char const* hwp_epb_str { "" };
    bool print_hwp_cfg { false };

    Cpuid const cpuid { };
    if (cpuid.vendor() == Cpuid::Vendor::INTEL &&
        cpuid.family_id() == 6 &&
        cpuid.model() == Cpuid::Model::KABY_LAKE_DESKTOP &&
        cpuid.hardware_coordination_feedback_cap())
    {
        Cpu_msr::energy_efficiency_optimization(false);
        eeo_str = " eeo=0";
        print_hwp_cfg = true;
    }
    if (cpuid.hwp()) {
        if (cpuid.hwp_notification()) {
            Cpu_msr::hwp_notification_irqs(false);
            hwp_irq_str = " hwp_irq=0";
            print_hwp_cfg = true;
        }
        Cpu_msr::hardware_pstates(true);
        hwp_str = " hwp=1";
        print_hwp_cfg = true;

        if (cpuid.hwp_energy_perf_pref()) {
            Cpu_msr::hwp_energy_perf_pref(Cpu_msr::Hwp_epp::PERFORMANCE);
            hwp_epp_str = " hwp_epp=0";
            print_hwp_cfg = true;
        }
        if (cpuid.hwp_energy_perf_bias()) {
            Cpu_msr::hwp_energy_perf_bias(Cpu_msr::Hwp_epb::PERFORMANCE);
            hwp_epb_str = " hwp_epb=0";
            print_hwp_cfg = true;
        }
    }
    if (print_hwp_cfg) {
        trace (TRACE_CPU, "HWP config for core %x.%x.%x:%s%s%s%s%s",
               Cpu::package[Cpu::id], Cpu::core[Cpu::id],
               Cpu::thread[Cpu::id], eeo_str, hwp_str, hwp_irq_str,
               hwp_epp_str, hwp_epb_str);
    }
}

void Cpu::check_features()
{
    unsigned top, tpp = 1, cpp = 1;

    uint32 eax, ebx, ecx, edx;

    cpuid (0, eax, ebx, ecx, edx);

    size_t v;
    for (v = sizeof (vendor_string) / sizeof (*vendor_string); --v;)
        if (*reinterpret_cast<uint32 const *>(vendor_string[v] + 0) == ebx &&
            *reinterpret_cast<uint32 const *>(vendor_string[v] + 4) == edx &&
            *reinterpret_cast<uint32 const *>(vendor_string[v] + 8) == ecx)
            break;

    vendor = Vendor (v);

    if (vendor == INTEL) {
        Msr::write<uint64>(Msr::IA32_BIOS_SIGN_ID, 0);
        platform[Cpu::id] = static_cast<unsigned>(Msr::read<uint64>(Msr::IA32_PLATFORM_ID) >> 50) & 7;
    }

    switch (static_cast<uint8>(eax)) {
        default:
            cpuid (0x7, 0, eax, features[3], ecx, edx);
            [[fallthrough]];
        case 0x6:
            cpuid (0x6, features[2], ebx, ecx, edx);
            [[fallthrough]];
        case 0x4 ... 0x5:
            cpuid (0x4, 0, eax, ebx, ecx, edx);
            cpp = (eax >> 26 & 0x3f) + 1;
            [[fallthrough]];
        case 0x1 ... 0x3:
            cpuid (0x1, eax, ebx, features[1], features[0]);
            family[Cpu::id]   = ((eax >> 8 & 0xf) + (eax >> 20 & 0xff)) & 0xff;
            model[Cpu::id]    = ((eax >> 4 & 0xf) + (eax >> 12 & 0xf0)) & 0xff;
            stepping[Cpu::id] =  eax & 0xf;
            brand    =  ebx & 0xff;
            top      =  ebx >> 24;
            tpp      =  ebx >> 16 & 0xff;
    }

    patch[Cpu::id] = static_cast<unsigned>(Msr::read<uint64>(Msr::IA32_BIOS_SIGN_ID) >> 32);

    cpuid (0x80000000, eax, ebx, ecx, edx);

    if (eax & 0x80000000) {
        switch (static_cast<uint8>(eax)) {
            default:
                cpuid (0x8000000a, Vmcb::svm_version, ebx, ecx, Vmcb::svm_feature);
                [[fallthrough]];
            case 0x4 ... 0x9:
                cpuid (0x80000004, name[8], name[9], name[10], name[11]);
                [[fallthrough]];
            case 0x3:
                cpuid (0x80000003, name[4], name[5], name[6], name[7]);
                [[fallthrough]];
            case 0x2:
                cpuid (0x80000002, name[0], name[1], name[2], name[3]);
                [[fallthrough]];
            case 0x1:
                cpuid (0x80000001, eax, ebx, features[5], features[4]);
                [[fallthrough]];
        }
    }

    if (feature (FEAT_CMP_LEGACY))
        cpp = tpp;

    unsigned tpc = tpp / cpp;
    unsigned long t_bits = bit_scan_reverse (tpc - 1) + 1;
    unsigned long c_bits = bit_scan_reverse (cpp - 1) + 1;

    thread[Cpu::id]  = (top            & ((1u << t_bits) - 1)) & 0xff;
    core[Cpu::id]    = (top >>  t_bits & ((1u << c_bits) - 1)) & 0xff;
    package[Cpu::id] = (top >> (t_bits + c_bits)) & 0xff;

    // Disable C1E on AMD Rev.F and beyond because it stops LAPIC clock
    if (vendor == AMD)
        if (family[Cpu::id] > 0xf || (family[Cpu::id] == 0xf && model[Cpu::id] >= 0x40))
            Msr::write (Msr::AMD_IPMR, Msr::read<uint32>(Msr::AMD_IPMR) & ~(3ul << 27));

    // enable PAT if available
    cpuid (0x1, eax, ebx, ecx, edx);
    if (edx & (1 << 16)) {
        uint32 cr_pat = Msr::read<uint32>(Msr::IA32_CR_PAT) & 0xffff00ff;

        cr_pat |= 1 << 8;
        Msr::write<uint32>(Msr::IA32_CR_PAT, cr_pat);
    } else
        trace (0, "warning: no PAT support");
}

void Cpu::setup_thermal()
{
    Msr::write (Msr::IA32_THERM_INTERRUPT, 0x10);
}

void Cpu::setup_sysenter()
{
#ifdef __i386__
    Msr::write<mword>(Msr::IA32_SYSENTER_CS,  SEL_KERN_CODE);
    Msr::write<mword>(Msr::IA32_SYSENTER_ESP, reinterpret_cast<mword>(&Tss::run.sp0));
    Msr::write<mword>(Msr::IA32_SYSENTER_EIP, reinterpret_cast<mword>(&entry_sysenter));
#else
    Msr::write<mword>(Msr::IA32_STAR,  static_cast<mword>(SEL_USER_CODE) << 48 | static_cast<mword>(SEL_KERN_CODE) << 32);
    Msr::write<mword>(Msr::IA32_LSTAR, reinterpret_cast<mword>(&entry_sysenter));
    Msr::write<mword>(Msr::IA32_FMASK, Cpu::EFL_DF | Cpu::EFL_IF | Cpu::EFL_NT | Cpu::EFL_TF);
#endif
}

void Cpu::setup_pcid()
{
#ifdef __x86_64__
    if (EXPECT_FALSE (Cmdline::nopcid))
#endif
        defeature (FEAT_PCID);

    if (EXPECT_FALSE (!feature (FEAT_PCID)))
        return;

    set_cr4 (get_cr4() | Cpu::CR4_PCIDE);
}

void Cpu::init()
{
    for (void (**func)() = &CTORS_L; func != &CTORS_C; (*func++)()) ;

    Gdt::build();
    Tss::build();

    // Initialize exception handling
    Gdt::load();
    Tss::load();
    Idt::load();

    Lapic::init_cpuid();

    // Initialize CPU number and check features
    check_features();

    Lapic::init(invariant_tsc());

    row = Console_vga::con.spinner (id);

    Paddr phys; mword attr;
    Pd::kern.Space_mem::loc[id] = Hptp (Hpt::current());
    Pd::kern.Space_mem::loc[id].lookup (CPU_LOCAL_DATA, phys, attr);
    Pd::kern.Space_mem::insert (Pd::kern.quota, HV_GLOBAL_CPUS + id * PAGE_SIZE, 0, Hpt::HPT_NX | Hpt::HPT_G | Hpt::HPT_W | Hpt::HPT_P, phys);
    Hpt::ord = min (Hpt::ord, feature (FEAT_1GB_PAGES) ? 26UL : 17UL);

    if (EXPECT_TRUE (feature (FEAT_ACPI)))
        setup_thermal();

    if (EXPECT_TRUE (feature (FEAT_SEP)))
        setup_sysenter();

    setup_pcid();

    mword cr4 = get_cr4();
    if (EXPECT_TRUE (feature (FEAT_SMEP)))
        cr4 |= Cpu::CR4_SMEP;
    if (EXPECT_TRUE (feature (FEAT_SMAP)))
        cr4 |= Cpu::CR4_SMAP;
    if (cr4 != get_cr4())
        set_cr4 (cr4);

    Vmcs::init();
    Vmcb::init();

    Mca::init();

    configure_hardware_pstates();

    trace (TRACE_CPU, "CORE:%x:%x:%x %x:%x:%x:%x [%x] %.48s", package[Cpu::id], core[Cpu::id], thread[Cpu::id], family[Cpu::id], model[Cpu::id], stepping[Cpu::id], platform[Cpu::id], patch[Cpu::id], reinterpret_cast<char *>(name));

    Hip::add_cpu();

    boot_lock++;
}
