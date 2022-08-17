// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from libunity.djinni

#pragma once

#include "djinni_support.hpp"
#include "mnemonic_record.hpp"

namespace djinni_generated {

class NativeMnemonicRecord final {
public:
    using CppType = ::MnemonicRecord;
    using JniType = jobject;

    using Boxed = NativeMnemonicRecord;

    ~NativeMnemonicRecord();

    static CppType toCpp(JNIEnv* jniEnv, JniType j);
    static ::djinni::LocalRef<JniType> fromCpp(JNIEnv* jniEnv, const CppType& c);

private:
    NativeMnemonicRecord();
    friend ::djinni::JniClass<NativeMnemonicRecord>;

    const ::djinni::GlobalRef<jclass> clazz { ::djinni::jniFindClass("unity_wallet/jniunifiedbackend/MnemonicRecord") };
    const jmethodID jconstructor { ::djinni::jniGetMethodID(clazz.get(), "<init>", "(Ljava/lang/String;Ljava/lang/String;J)V") };
    const jfieldID field_mPhraseWithBirthNumber { ::djinni::jniGetFieldID(clazz.get(), "mPhraseWithBirthNumber", "Ljava/lang/String;") };
    const jfieldID field_mPhrase { ::djinni::jniGetFieldID(clazz.get(), "mPhrase", "Ljava/lang/String;") };
    const jfieldID field_mBirthNumber { ::djinni::jniGetFieldID(clazz.get(), "mBirthNumber", "J") };
};

}  // namespace djinni_generated
